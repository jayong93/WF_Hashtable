#include <utility>
#include <vector>
#include <atomic>
#include <cmath>
#include <memory>
#include <algorithm>
#include <cassert>
#include <optional>
#include <functional>
#include <iostream>
#include <unordered_set>
#include <array>

using namespace std;

static atomic_uint id_counter{ 0 };
static thread_local int thread_id = id_counter.fetch_add(1, memory_order_relaxed);

static constexpr unsigned BSTATE_ITEM_NUM = 4;

template <typename Key, typename Value, typename Hasher, typename HashType>
class WF_HashTable
{
	enum class OP
	{
		Insert,
		Remove
	};

	struct Operation
	{
		OP op;
		HashType key;
		Value value;
		size_t seq_num;
	};

	struct Result
	{
		enum class Status
		{
			True,
			False,
			Fail
		} status;
		size_t seq_num{ 0 };

		explicit Result() : status{ Status::True }, seq_num{ 0 } {}
	};

	struct BState
	{
		using Status = typename Result::Status;
		array<optional<pair<HashType, Value>>, BSTATE_ITEM_NUM> items;
		vector<bool> applied;
		vector<Result> results;

		explicit BState(unsigned thread_num)
		{
			applied.reserve(thread_num);
			results.reserve(thread_num);
			for (auto i = 0; i < thread_num; ++i)
			{
				applied.emplace_back(false);
				results.emplace_back();
			}
		}

		Status insert(HashType key, const Value& val)
		{
			// key가 없을거라고 가정하고 시작
			// insert는 key가 없어야 성공이므로 true로 초기화
			Status status = Result::Status::True;

			auto empty_it = iterate([&status, key, &val](auto& item) {
				// key가 있으면 update
				if (item->first == key)
				{
					item->second = val;
					status = Status::False;
				}
				});
			// BState가 꽉 차있으면 무조건 Fail
			if (empty_it == items.end())
				return Status::Fail;
			// key가 없고 빈자리가 있으면 삽입
			else if (status == Status::True)
			{
				empty_it->emplace(key, val);
			}
			return status;
		}

		Status remove(HashType key)
		{
			// key가 없을거라고 가정
			// remove는 key가 있어야 성공이므로 false로 초기화
			Status status = Status::False;
			// BState가 꽉 차있으면 무조건 Fail
			auto empty_it = iterate([&status, key](auto& item) {
				if (item->first == key)
				{
					item.reset();
					status = Status::True;
				}
				});
			if (empty_it == items.end())
				return Status::Fail;

			return status;
		}

		bool is_full() const
		{
			return all_of(items.begin(), items.end(), [](const optional<pair<HashType, Value>>& item) { return bool(item); });
		}

	private:
		// item을 순회하면서 빈자리가 있는 경우 반환, 비어있지 않은 item에 대해 lambda 수행
		template <typename F>
		auto iterate(F func)
		{
			auto empty_it = items.end();
			for (auto it = items.begin(); it != items.end(); ++it)
			{
				auto& item = *it;
				if (!item)
				{
					if (empty_it == items.end())
						empty_it = it;
					continue;
				}
				func(item);
			}

			return empty_it;
		}
	};

	struct Bucket
	{
		size_t prefix;
		unsigned depth;
		atomic<BState*> state;
		vector<bool> toggle;

		explicit Bucket(unsigned depth, unsigned thread_num) : prefix{ 0 }, depth{ depth }, state{ new BState{thread_num} }
		{
			toggle.reserve(thread_num);
			for (auto i = 0; i < thread_num; ++i)
			{
				toggle.emplace_back(false);
			}
		}
		Bucket(const Bucket& other) : prefix{ other.prefix }, depth{ other.depth }, state{ other.state.load(memory_order_acquire) }, toggle{ other.toggle } {}
		~Bucket()
		{
			auto s = state.load(memory_order_relaxed);
			if (s != nullptr)
			{
				delete s;
			}
		}

		Bucket& operator=(const Bucket& other)
		{
			prefix = other.prefix;
			depth = other.depth;
			state = other.state.load(memory_order_acquire);
			toggle = other.toggle;
		}
	};

	template<typename T>
	struct CopyableAtomic {
		atomic<T*> value;

		CopyableAtomic<T>() : value{ nullptr } {}
		CopyableAtomic<T>(T* ptr) : value{ ptr } {}
		CopyableAtomic<T>(const CopyableAtomic<T>& other) : value{ other.value.load(memory_order_relaxed) } {}
		atomic<T*>& operator*() { return value; }
		atomic<T*>* operator->() { return &value; }
	};

	struct DState
	{
		unsigned depth;
		vector<CopyableAtomic<Bucket>> dir;

		explicit DState(unsigned depth, unsigned thread_num) : depth{ depth }, dir{ (1u << depth), nullptr }
		{
			unsigned i;
			Bucket* bucket = new Bucket{ 1u, thread_num };
			bucket->prefix = 0;
			for (i = 0; i < (1 << (depth - 1)); ++i)
			{
				dir[i]->store(bucket, memory_order_relaxed);
			}

			bucket = new Bucket{ 1u, thread_num };
			bucket->prefix = 1;
			for (; i < (1 << depth); ++i)
			{
				dir[i]->store(bucket, memory_order_relaxed);
			}
		}

		void resize(unsigned new_depth)
		{
			if (new_depth <= depth)
				return;
			vector<CopyableAtomic<Bucket>> new_dir{ (1u << new_depth) };
			for (auto i = 0; i < (1 << new_depth); ++i)
			{
				for (auto entry : dir)
				{
					Bucket* bucket = entry->load(memory_order_relaxed);
					const auto dir_prefix = (i >> (new_depth - bucket->depth));
					if (bucket->prefix == dir_prefix)
					{
						new_dir[i]->store(bucket, memory_order_relaxed);
						break;
					}
					else if (bucket->prefix < dir_prefix) {
						break;
					}
				}
			}

			depth = new_depth;
			dir = move(new_dir);
		}
	};

public:
	WF_HashTable<Key, Value, Hasher, HashType>(unsigned thread_num) : thread_num{ thread_num }, help{ thread_num }, op_seq_nums{ thread_num, 0 }, table{ new DState{INITIAL_DEPTH, thread_num} }, retired_lists{ thread_num }, thread_counter{ thread_num, 0 }, global_epoch{ 0 }
	{
		for (auto i = 0; i < thread_num; ++i)
		{
			thread_epochs.emplace_back(new atomic_uint64_t{ 0 });
		}
	}

	~WF_HashTable<Key, Value, Hasher, HashType>()
	{
		// DState *l_table = table.load(memory_order_acquire);
		// Bucket *prev_bucket = nullptr;
		// for (auto entry : l_table->dir)
		// {
		//     Bucket *bucket = entry->load(memory_order_acquire);
		//     if (prev_bucket == bucket)
		//     {
		//         continue;
		//     }
		//     else if (prev_bucket == nullptr)
		//     {
		//         prev_bucket = bucket;
		//     }
		//     else {
		//         delete prev_bucket;
		//         prev_bucket = bucket;
		//     }
		// }
		// delete prev_bucket;
		// delete l_table;

		// for (auto &dstates : dstates_retired)
		// {
		//     for (auto retired : dstates)
		//     {
		//         delete retired.ptr;
		//     }
		// }
		// for (auto &buckets : buckets_retired)
		// {
		//     for (auto retired : buckets)
		//     {
		//         delete retired.ptr;
		//     }
		// }
		// for (auto &bstates : bstates_retired)
		// {
		//     for (auto retired : bstates)
		//     {
		//         delete retired.ptr;
		//     }
		// }
		// for (auto p_epoch : thread_epochs)
		// {
		//     delete p_epoch;
		// }
	}

	void announce(OP op, HashType key, const Value& value, size_t seq_num)
	{
		help[get_tid()] = new Operation{ op, key, value, seq_num };
	}

	typename Result::Status exec_on_bucket(BState* b, const Operation& op)
	{
		typename Result::Status result;

		if (op.op == OP::Insert)
		{
			result = b->insert(op.key, op.value);
		}
		else
		{
			result = b->remove(op.key);
		}
		return result;
	}

	bool update_bucket(Bucket* bucket)
	{
		auto old_bstate = bucket->state.load(memory_order_acquire);
		auto new_bstate = new BState{ *old_bstate };
		auto toggle = bucket->toggle;

		for (int i = 0; i < thread_num; ++i)
		{
			// thread i가 update중이 아니면 skip
			if (toggle[i] == new_bstate->applied[i])
				continue;

			Result& result = new_bstate->results[i];
			if (help[i] == nullptr)
				continue;
			const Operation& help_op = *help[i];
			if (result.seq_num < help_op.seq_num)
			{
				result.status = exec_on_bucket(new_bstate, help_op);
				if (result.status != Result::Status::Fail)
				{
					result.seq_num = help_op.seq_num;
				}
			}
		}
		new_bstate->applied = toggle;
		auto is_successed = bucket->state.compare_exchange_strong(old_bstate, new_bstate);
		if (is_successed)
		{
			retire(old_bstate);
		}
		return is_successed;
	}

	void apply_op(HashType key)
	{
		DState* local_table = table.load(memory_order_acquire);
		Bucket* bucket = local_table->dir[get_prefix(key, local_table->depth)]->load(memory_order_acquire);
		// 현재 thread가 이 bucket에 update를 시도한다는 것을 알림
		// 충돌하는 다른 thread들은 이걸 보고 도와줌
		auto toggle = bucket->toggle[get_tid()];
		bucket->toggle[get_tid()] = !toggle;

		for (int i = 0; i < 2; ++i)
		{
			if (update_bucket(bucket))
				break;
		}
	}

	pair<Bucket*, Bucket*> split_bucket(const Bucket& from)
	{
		const BState& org_state = *(from.state.load(memory_order_acquire));
		Bucket* new_b1 = new Bucket{ from };
		new_b1->depth = from.depth + 1;
		new_b1->prefix = from.prefix << 1;
		BState* b1_state = new BState{ (unsigned)org_state.applied.size() };
		b1_state->results = org_state.results;
		b1_state->applied = new_b1->toggle;
		new_b1->state.store(b1_state, memory_order_release);

		Bucket* new_b2 = new Bucket{ *new_b1 };
		new_b2->prefix = new_b1->prefix + 1;
		BState* b2_state = new BState{ *b1_state };
		new_b2->state.store(b2_state, memory_order_release);

		for (auto& item : org_state.items)
		{
			if (!item)
				continue;
			const auto& [key, value] = *item;
			if (get_prefix(key, new_b1->depth) == new_b1->prefix)
			{
				auto it = find_if(b1_state->items.begin(), b1_state->items.end(), [](auto& item) {
					return !item;
					});
				assert(it != b1_state->items.end() && "There is no place to insert item");
				it->emplace(key, value);
			}
			else
			{
				auto it = find_if(b2_state->items.begin(), b2_state->items.end(), [](auto& item) {
					return !item;
					});
				assert(it != b2_state->items.end() && "There is no place to insert item");
				it->emplace(key, value);
			}
		}

		return make_pair(new_b1, new_b2);
	}

	void update_directory(DState& table, Bucket& buck1, Bucket& buck2)
	{
		Bucket* buckets[2] = { &buck1, &buck2 };
		for (auto b : buckets)
		{
			if (table.depth < b->depth)
			{
				table.resize(table.depth + 1);
			}
			for (auto i = 0; i < table.dir.size(); ++i)
			{
				auto entry_prefix = i >> (table.depth - b->depth);
				if (entry_prefix == b->prefix)
				{
					table.dir[i]->store(b, memory_order_relaxed);
				}
				else if (b->prefix < entry_prefix)
					break;
			}
		}
	}

	vector<Bucket*> apply_pending_resize(DState& table, const Bucket& bucket_full)
	{
		vector<Bucket*> retired_buckets;
		for (auto i = 0; i < help.size(); ++i)
		{
			if (help[i] == nullptr)
				continue;
			const Operation& op = *help[i];
			if (get_prefix(op.key, bucket_full.depth) != bucket_full.prefix)
				continue;
			const BState& state = *bucket_full.state.load(memory_order_relaxed);
			if (state.results[i].seq_num >= op.seq_num)
				continue;

			Bucket* dest = table.dir[get_prefix(op.key, table.depth)]->load(memory_order_relaxed);
			BState* dest_state = dest->state.load(memory_order_relaxed);
			while (dest_state->is_full())
			{
				auto [new_buck1, new_buck2] = split_bucket(*dest);
				update_directory(table, *new_buck1, *new_buck2);
				retired_buckets.emplace_back(dest);
				dest = table.dir[get_prefix(op.key, table.depth)]->load(memory_order_relaxed);
				dest_state = dest->state.load(memory_order_relaxed);
			}
			dest_state->results[i].status = exec_on_bucket(dest_state, op);
			dest_state->results[i].seq_num = op.seq_num;
		}
		return retired_buckets;
	}

	vector<Bucket*> update_new_table(DState& table, int thread_id)
	{
		vector<Bucket*> retired_buckets;
		if (help[thread_id] == nullptr)
			return retired_buckets;
		const Operation& op = *help[thread_id];
		Bucket* bucket = table.dir[get_prefix(op.key, table.depth)]->load(memory_order_relaxed);
		BState* state = bucket->state.load(memory_order_relaxed);
		if (state->is_full() && state->results[thread_id].seq_num < op.seq_num)
		{
			retired_buckets = apply_pending_resize(table, *bucket);
		}
		return retired_buckets;
	}

	void resize()
	{
		for (auto i = 0; i < 2; ++i)
		{
			vector<Bucket*> retired_buckets;
			DState* old_table = table.load(memory_order_relaxed);
			DState* new_table = new DState{ *old_table };

			for (auto i = 0; i < help.size(); ++i)
			{
				auto buckets = update_new_table(*new_table, i);
				retired_buckets.insert(retired_buckets.end(), buckets.begin(), buckets.end());
			}

			if (true == table.compare_exchange_strong(old_table, new_table))
			{
				for (auto bucket : retired_buckets)
				{
					retire(bucket);
				}
				retire(old_table);
				break;
			}
		}
	}

	void resize_if_needed(HashType key, size_t seq_num)
	{
		DState* local_table = table.load(memory_order_acquire);
		Bucket* bucket = local_table->dir[get_prefix(key, local_table->depth)]->load(memory_order_acquire);
		BState* state = bucket->state.load(memory_order_acquire);

		if (state->results[get_tid()].seq_num != seq_num)
		{
			resize();
		}
	}

	typename Result::Status insert(Key&& key, const Value& value)
	{
		start_op();
		// key에서 hash 값 구하기
		HashType hash_key = Hasher{}(key);
		const auto tid = get_tid();
		// help에 Op 등록 => 다른 thread들이 도울 수 있게
		auto seq_num = ++op_seq_nums[tid];
		announce(OP::Insert, hash_key, value, seq_num);
		// Wait-Free Op 적용
		apply_op(hash_key);
		// Resize가 필요하면 Resize
		resize_if_needed(hash_key, seq_num);

		auto local_table = table.load(memory_order_acquire);
		auto status = local_table->dir[get_prefix(hash_key, local_table->depth)]->load(memory_order_relaxed)->state.load(memory_order_relaxed)->results[tid].status;
		end_op();
		return status;
	}

	typename Result::Status remove(Key&& key)
	{
		start_op();
		// key에서 hash 값 구하기
		HashType hash_key = Hasher{}(key);
		const auto tid = get_tid();
		// help에 Op 등록 => 다른 thread들이 도울 수 있게
		auto seq_num = ++op_seq_nums[tid];
		announce(OP::Remove, hash_key, Value{}, seq_num);
		// Wait-Free Op 적용
		apply_op(hash_key);
		// Resize가 필요하면 Resize
		resize_if_needed(hash_key, seq_num);

		auto local_table = table.load(memory_order_acquire);
		auto status = local_table->dir[get_prefix(hash_key, local_table->depth)]->load(memory_order_relaxed)->state.load(memory_order_relaxed)->results[tid].status;
		end_op();
		return status;
	}

	optional<Value> lookup(const Key& key)
	{
		start_op();
		HashType hash_key = Hasher{}(key);
		DState* local_table = table.load(memory_order_acquire);
		BState* state = local_table->dir[get_prefix(hash_key, local_table->depth)]
			->load(memory_order_acquire)
			->state.load(memory_order_acquire);

		auto it = find_if(state->items.begin(), state->items.end(), [hash_key](auto& item) {
			return item && item->first == hash_key;
			});
		if (it == state->items.end())
		{
			end_op();
			return nullopt;
		}
		auto ret_val = (*it)->second;
		end_op();
		return ret_val;
	}

	void dump()
	{
		DState* local_table = table.load(memory_order_acquire);
		printf("Dump(<HashKey, Value>):\n");
		for (const auto& dir_entry : local_table->dir)
		{
			Bucket* bucket = dir_entry->load(memory_order_relaxed);
			BState* state = bucket->state.load(memory_order_relaxed);
			for (const auto& item : state->items)
			{
				if (item)
				{
					cout << "<" << item->first << ", " << item->second << ">, ";
				}
			}
		}
		cout << endl;
	}

	static constexpr unsigned INITIAL_DEPTH = 4;

private:
	size_t get_prefix(HashType key, unsigned depth) const
	{
		assert(depth < sizeof(HashType) * 8 && "depth is bigger than bit-wise size of a key");
		return (key >> (sizeof(HashType) * 8 - depth));
	}

	int get_tid() const
	{
		return thread_id % thread_num;
	}

	template <typename T>
	struct EpochNode
	{
		T* ptr;
		uint64_t retired_epoch;

		EpochNode<T>() : ptr{ nullptr }, retired_epoch{ 0 } {}
		EpochNode<T>(T* ptr, uint64_t epoch) : ptr{ ptr }, retired_epoch{ epoch } {}
		EpochNode<T>(const EpochNode<T>& other) : ptr{ other.ptr }, retired_epoch{ other.retired_epoch } {}
	};

	struct RetiredList {
		vector<EpochNode<DState>> dstates;
		vector<EpochNode<Bucket>> buckets;
		vector<EpochNode<BState>> bstates;
	};

	void start_op()
	{
		auto tid = get_tid();
		thread_epochs[tid]->store(global_epoch.load(memory_order_relaxed), memory_order_release);
	}
	void end_op()
	{
		auto tid = get_tid();
		thread_epochs[tid]->store(UINT64_MAX, memory_order_release);
	}
	void retire_(int tid, DState* ptr, uint64_t epoch)
	{
		retired_lists[tid].dstates.emplace_back(ptr, epoch);
	}
	void retire_(int tid, Bucket* ptr, uint64_t epoch)
	{
		retired_lists[tid].buckets.emplace_back(ptr, epoch);
	}
	void retire_(int tid, BState* ptr, uint64_t epoch)
	{
		retired_lists[tid].bstates.emplace_back(ptr, epoch);
	}
	void empty(int tid)
	{
		auto min_epoch = UINT64_MAX;
		for (auto epoch : thread_epochs)
		{
			auto e = epoch->load(memory_order_acquire);
			if (e < min_epoch)
			{
				min_epoch = e;
			}
		}

		RetiredList& r_list = retired_lists[tid];

		remove_retired(r_list.dstates, min_epoch);
		remove_retired(r_list.buckets, min_epoch);
		remove_retired(r_list.bstates, min_epoch);
	}
	template <typename T>
	void remove_retired(vector<EpochNode<T>>& list, uint64_t min_epoch)
	{
		auto removed_it = remove_if(list.begin(), list.end(), [min_epoch](auto& r_node) {
			if (r_node.retired_epoch < min_epoch)
			{
				delete r_node.ptr;
				return true;
			}
			return false;
			});

		list.erase(removed_it, list.end());
	}
	template <typename T>
	void retire(T* ptr)
	{
		auto tid = get_tid();
		retire_(tid, ptr, global_epoch.load(memory_order_relaxed));
		auto& counter = thread_counter[tid];
		counter++;
		if (counter % EPOCH_INCREASE_RATE == 0)
			global_epoch.fetch_add(1, memory_order_relaxed);
		if (counter % EMPTY_RATE == 0)
			empty(tid);
	}

	atomic<DState*> table;
	vector<Operation*> help;
	vector<size_t> op_seq_nums;

	vector<RetiredList> retired_lists;
	vector<atomic_uint64_t*> thread_epochs;
	vector<uint64_t> thread_counter;
	atomic_uint64_t global_epoch;

	static constexpr uint64_t EPOCH_INCREASE_RATE = 50;
	static constexpr uint64_t EMPTY_RATE = 100;
	const unsigned thread_num;
};