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

using namespace std;

static atomic_uint id_counter{0};
static thread_local int thread_id = id_counter.fetch_add(1, memory_order_relaxed);

static constexpr unsigned BSTATE_ITEM_NUM = 4;
static constexpr uint64_t EPOCH_INCREASE_RATE = 50;
static constexpr uint64_t EMPTY_RATE = 100;

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
        size_t key;
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
        size_t seq_num{0};

        explicit Result() : status{Status::True}, seq_num{0} {}
    };

    struct BState
    {
        using Status = typename Result::Status;
        array<optional<pair<size_t, Value>>, BSTATE_ITEM_NUM> items;
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

        Status insert(size_t key, const Value &val)
        {
            // key가 없을거라고 가정하고 시작
            // insert는 key가 없어야 성공이므로 true로 초기화
            Status status = Result::Status::True;

            auto empty_it = iterate([&status, key, &val](auto &item) {
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

        Status remove(size_t key)
        {
            // key가 없을거라고 가정
            // remove는 key가 있어야 성공이므로 false로 초기화
            Status status = Status::False;
            // BState가 꽉 차있으면 무조건 Fail
            auto empty_it = iterate([&status, key](auto &item) {
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
            return all_of(items.begin(), items.end(), [](const optional<pair<size_t, Value>> &item) { return bool(item); });
        }

    private:
        // item을 순회하면서 빈자리가 있는 경우 반환, 비어있지 않은 item에 대해 lambda 수행
        template <typename F>
        auto iterate(F func)
        {
            auto empty_it = items.end();
            for (auto it = items.begin(); it != items.end(); ++it)
            {
                auto &item = *it;
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
        atomic<BState *> state;
        vector<bool> toggle;

        explicit Bucket(unsigned depth, unsigned thread_num) : prefix{0}, depth{depth}, state{new BState{thread_num}}
        {
            toggle.reserve(thread_num);
            for (auto i = 0; i < thread_num; ++i)
            {
                toggle.emplace_back(false);
            }
        }
        explicit Bucket(const Bucket &other) : prefix{other.prefix}, depth{other.depth}, state{other.state.load(memory_order_acquire)}, toggle{other.toggle} {}
        ~Bucket() {
            auto s = state.load(memory_order_relaxed);
            if (s != nullptr)
            {
                delete s;
            }
        }

        Bucket &operator=(const Bucket &other)
        {
            prefix = other.prefix;
            depth = other.depth;
            state = other.state.load(memory_order_acquire);
            toggle = other.toggle;
        }
    };

    struct DState
    {
        unsigned depth;
        vector<atomic<Bucket *> *> dir;

        DState(unsigned depth, unsigned thread_num) : depth{depth}, dir{(1u << depth), nullptr}
        {
            unsigned i;
            for (i = 0; i < (1 << depth - 1); ++i)
            {
                Bucket *bucket = new Bucket{1, thread_num};
                bucket->prefix = 0;
                dir[i] = new atomic<Bucket *>{bucket};
            }
            for (; i < (1 << depth); ++i)
            {
                Bucket *bucket = new Bucket{1, thread_num};
                bucket->prefix = 1;
                dir[i] = new atomic<Bucket *>{bucket};
            }
        }
        DState(const DState &other) : depth{other.depth}, dir{(1u << depth), nullptr}
        {
            for (auto i = 0; i < dir.size(); ++i)
            {
                dir[i] = new atomic<Bucket *>{other.dir[i]->load(memory_order_relaxed)};
            }
        }
        ~DState()
        {
            for (auto p : dir)
            {
                delete p;
            }
        }

        void resize(unsigned new_depth)
        {
            if (new_depth <= depth)
                return;
            vector<atomic<Bucket *> *> new_dir;
            for (auto i = 0; i < (1 << new_depth); ++i)
            {
                atomic<Bucket *> *new_entry = nullptr;
                for (auto entry : dir)
                {
                    Bucket *bucket = entry->load(memory_order_relaxed);
                    if (bucket->prefix == (i >> (new_depth - bucket->depth)))
                    {
                        new_entry = new atomic<Bucket *>{bucket};
                    }
                }
                assert(new_entry != nullptr && "a new directory entry has no bucket");
                new_dir.emplace_back(new_entry);
            }

            depth = new_depth;
            dir = move(new_dir);
        }
    };

public:
    WF_HashTable<Key, Value, Hasher, HashType>(unsigned thread_num) : thread_num{thread_num}, help{thread_num}, op_seq_nums{thread_num, 0}, table{new DState{INITIAL_DEPTH, thread_num}}, dstates_retired{thread_num}, buckets_retired{thread_num}, bstates_retired{thread_num}
    {
    }

    ~WF_HashTable<Key, Value, Hasher, HashType>()
    {
        DState &l_table = *table.load(memory_order_acquire);
        for (auto entry : l_table.dir)
        {
            Bucket* bucket = entry->load(memory_order_acquire);
            delete bucket;
            delete entry;
        }

        for(auto& dstates : dstates_retired) {
            for(auto ptr : dstates) {
                delete ptr;
            }
        }
        for(auto& buckets : buckets_retired) {
            for(auto ptr : buckets) {
                delete ptr;
            }
        }
        for(auto& bstates : bstates_retired) {
            for(auto ptr : bstates) {
                delete ptr;
            }
        }
    }

    void announce(OP op, size_t key, const Value &value, size_t seq_num)
    {
        help[get_tid()] = new Operation{op, key, value, seq_num};
    }

    typename Result::Status exec_on_bucket(BState *b, const Operation &op)
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

    bool update_bucket(Bucket *bucket)
    {
        auto old_bstate = bucket->state.load(memory_order_acquire);
        auto new_bstate = new BState{*old_bstate};
        auto toggle = bucket->toggle;

        for (int i = 0; i < thread_num; ++i)
        {
            // thread i가 update중이 아니면 skip
            if (toggle[i] == new_bstate->applied[i])
                continue;

            Result &result = new_bstate->results[i];
            if (help[i] == nullptr)
                continue;
            const Operation &help_op = *help[i];
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
        return bucket->state.compare_exchange_strong(old_bstate, new_bstate);
    }

    void apply_op(HashType key)
    {
        DState *local_table = table.load(memory_order_acquire);
        Bucket *bucket = local_table->dir[get_prefix(key, local_table->depth)]->load(memory_order_acquire);
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

    pair<Bucket *, Bucket *> split_bucket(const Bucket &from)
    {
        const BState &org_state = *(from.state.load(memory_order_acquire));
        Bucket *new_b1 = new Bucket{from};
        new_b1->depth = from.depth + 1;
        new_b1->prefix = from.prefix << 1;
        BState *b1_state = new BState{(unsigned)org_state.applied.size()};
        b1_state->results = org_state.results;
        b1_state->applied = new_b1->toggle;
        new_b1->state.store(b1_state, memory_order_release);

        Bucket *new_b2 = new Bucket{*new_b1};
        new_b2->prefix = new_b1->prefix + 1;
        BState *b2_state = new BState{*b1_state};
        new_b2->state.store(b2_state, memory_order_release);

        for (auto &item : org_state.items)
        {
            if (!item)
                continue;
            const auto &[key, value] = *item;
            if (get_prefix(key, new_b1->depth) == new_b1->prefix)
            {
                auto it = find_if(b1_state->items.begin(), b1_state->items.end(), [](auto &item) {
                    return !item;
                });
                assert(it != b1_state->items.end() && "There is no place to insert item");
                it->emplace(key, value);
            }
            else
            {
                auto it = find_if(b2_state->items.begin(), b2_state->items.end(), [](auto &item) {
                    return !item;
                });
                assert(it != b2_state->items.end() && "There is no place to insert item");
                it->emplace(key, value);
            }
        }

        return make_pair(new_b1, new_b2);
    }

    void update_directory(DState &table, Bucket &buck1, Bucket &buck2)
    {
        Bucket *buckets[2] = {&buck1, &buck2};
        for (auto b : buckets)
        {
            if (table.depth < b->depth)
            {
                table.resize(table.depth + 1);
            }
            for (auto i = 0; i < table.dir.size(); ++i)
            {
                if (i >> (table.depth - b->depth) == b->prefix)
                {
                    table.dir[i]->store(b, memory_order_relaxed);
                }
            }
        }
    }

    void apply_pending_resize(DState &table, const Bucket &bucket_full)
    {
        for (auto i = 0; i < help.size(); ++i)
        {
            if (help[i] == nullptr)
                continue;
            const Operation &op = *help[i];
            if (get_prefix(op.key, bucket_full.depth) != bucket_full.prefix)
                continue;
            const BState &state = *bucket_full.state.load(memory_order_relaxed);
            if (state.results[i].seq_num >= op.seq_num)
                continue;

            Bucket *dest = table.dir[get_prefix(op.key, table.depth)]->load(memory_order_relaxed);
            BState *dest_state = dest->state.load(memory_order_relaxed);
            while (dest_state->is_full())
            {
                auto [new_buck1, new_buck2] = split_bucket(*dest);
                update_directory(table, *new_buck1, *new_buck2);
                dest = table.dir[get_prefix(op.key, table.depth)]->load(memory_order_relaxed);
                dest_state = dest->state.load(memory_order_relaxed);
            }
            dest_state->results[i].status = exec_on_bucket(dest_state, op);
            dest_state->results[i].seq_num = op.seq_num;
        }
    }

    void update_new_table(DState &table, int thread_id)
    {
        if (help[thread_id] == nullptr)
            return;
        const Operation &op = *help[thread_id];
        Bucket *bucket = table.dir[get_prefix(op.key, table.depth)]->load(memory_order_relaxed);
        BState *state = bucket->state.load(memory_order_relaxed);
        if (state->is_full() && state->results[thread_id].seq_num < op.seq_num)
        {
            apply_pending_resize(table, *bucket);
        }
    }

    void resize()
    {
        for (auto i = 0; i < 2; ++i)
        {
            DState *old_table = table.load(memory_order_relaxed);
            DState *new_table = new DState{*old_table};

            for (auto i = 0; i < help.size(); ++i)
            {
                update_new_table(*new_table, i);
            }

            if (true == table.compare_exchange_strong(old_table, new_table))
                break;
        }
    }

    void resize_if_needed(HashType key, HashType seq_num)
    {
        DState *local_table = table.load(memory_order_acquire);
        Bucket *bucket = local_table->dir[get_prefix(key, local_table->depth)]->load(memory_order_acquire);
        BState *state = bucket->state.load(memory_order_acquire);

        if (state->results[get_tid()].seq_num != seq_num)
        {
            resize();
        }
    }

    typename Result::Status insert(Key &&key, const Value &value)
    {
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
        return local_table->dir[get_prefix(hash_key, local_table->depth)]->load(memory_order_release)->state.load(memory_order_release)->results[tid].status;
    }

    typename Result::Status remove(Key &&key)
    {
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
        return local_table->dir[get_prefix(hash_key, local_table->depth)]->load(memory_order_release)->state.load(memory_order_release)->results[tid].status;
    }

    optional<Value> lookup(const Key &key)
    {
        HashType hash_key = Hasher{}(key);
        DState *local_table = table.load(memory_order_acquire);
        BState *state = local_table->dir[get_prefix(hash_key, local_table->depth)]
                            ->load(memory_order_acquire)
                            ->state.load(memory_order_acquire);

        auto it = find_if(state->items.begin(), state->items.end(), [hash_key](auto &item) {
            return item && item->first == hash_key;
        });
        if (it == state->items.end())
        {
            return nullopt;
        }
        return (*it)->second;
    }

    void dump()
    {
        DState *local_table = table.load(memory_order_acquire);
        printf("Dump(<HashKey, Value>):\n");
        for (const auto &dir_entry : local_table->dir)
        {
            Bucket *bucket = dir_entry->load(memory_order_relaxed);
            BState *state = bucket->state.load(memory_order_relaxed);
            for (const auto &item : state->items)
            {
                if (item)
                {
                    cout << "<" << item->first << ", " << item->second << ">, ";
                }
            }
        }
        cout << endl;
    }

    static constexpr unsigned INITIAL_DEPTH = 2;

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

    atomic<DState *> table;
    vector<Operation *> help;
    vector<size_t> op_seq_nums;
    vector<vector<DState*>> dstates_retired;
    vector<vector<Bucket*>> buckets_retired;
    vector<vector<BState*>> bstates_retired;
    vector<uint64_t> thread_epochs;
    atomic_uint64_t global_epoch;

    const unsigned thread_num;
};