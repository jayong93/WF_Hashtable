#include <utility>
#include <vector>
#include <atomic>
#include <cmath>
#include <memory>
#include <algorithm>
#include <cassert>
#include <optional>

using namespace std;

static atomic_uint id_counter{0};
static thread_local int thread_id = id_counter.fetch_add(1, memory_order_relaxed);

static constexpr unsigned BSTATE_ITEM_NUM = 4;
template <typename Hasher, typename Key, typename Value>
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
    };

    struct BState
    {
        using Status = typename Result::Status;
        array<optional<pair<size_t, Value>>, BSTATE_ITEM_NUM> items;
        vector<atomic_bool> applied;
        vector<Result> results;

        BState(unsigned thread_num) : applied{thread_num}, results{thread_num} {}

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
                (*empty_it)->emplace(val);
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
        BState *state;
        vector<atomic_bool> toggle;

        Bucket(unsigned depth, unsigned thread_num) : prefix{0}, depth{depth}, state{new BState{thread_num}}, toggle{thread_num} {}
        Bucket(const Bucket &other) : prefix{other.prefix}, depth{other.depth}, state{new BState{*other.state}}, toggle{other.toggle} {}
        Bucket &operator=(const Bucket &other)
        {
            prefix = other.prefix;
            depth = other.depth;
            state = new BState{*other.state};
            toggle = other.toggle;
        }
    };

    struct DState
    {
        unsigned depth;
        vector<Bucket *> dir;

        DState(unsigned depth) : depth{depth}, dir{(size_t)pow(2, depth)} {}
    };

public:
    WF_HashTable<Hasher, Key, Value>(unsigned thread_num) : thread_num{thread_num}, help{thread_num}, table{new DState{INITIAL_DEPTH}}
    {
    }

    void announce(OP op, size_t key, const Value &value, size_t seq_num)
    {
        help[get_tid()] = Operation{op, key, value, seq_num};
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

    void update_bucket(Bucket *bucket)
    {
        auto old_bstate = bucket->state;
        auto new_bstate = new BState{*old_bstate};
        auto toggle = bucket->toggle;

        for (int i = 0; i < thread_num; ++i)
        {
            // thread i가 update중이 아니면 skip
            if (toggle[i] == new_bstate->applied[i])
                continue;

            Result &result = new_bstate->results[i];
            const Operation &help_op = help[i];
            if (result.seq_num < help_op.seq_num)
            {
                result.status = exec_on_bucket(new_bstate, help_op);
                if (result.status != Result::Status::Fail)
                {
                    result.seq_num = help_op.seq_num;
                }
            }
        }
    }

    void apply_op(size_t key)
    {
        DState *local_table = table.load(memory_order_acquire);
        Bucket *bucket = local_table->dir[get_prefix(key, local_table->depth)];
        // 현재 thread가 이 bucket에 update를 시도한다는 것을 알림
        // 충돌하는 다른 thread들은 이걸 보고 도와줌
        bucket->toggle[get_tid()].fetch_xor(true, memory_order_relaxed);

        for (int i = 0; i < 2; ++i)
        {
            update_bucket(bucket);
        }
    }

    void resize_if_needed()
    {
    }

    typename Result::Status insert(Key &&key, const Value &value)
    {
        // key에서 hash 값 구하기
        size_t hash_key = Hasher{}(key);
        // help에 Op 등록 => 다른 thread들이 도울 수 있게
        auto seq_num = op_seq_num.fetch_add(1, memory_order_relaxed);
        announce(OP::Insert, hash_key, value, seq_num);
        // Wait-Free Op 적용
        apply_op(hash_key);
        // Resize가 필요하면 Resize
        resize_if_needed();

        auto local_table = table.load(memory_order_acquire);
        return local_table->dir[local_table->get_prefix(hash_key)].state->results[get_tid()].status;
    }

    static constexpr unsigned INITIAL_DEPTH = 2;

private:
    size_t get_prefix(size_t key, unsigned depth) const
    {
        assert(depth < sizeof(size_t) * 8 && "depth is bigger than bit-wise size of a key");
        return (key >> (sizeof(size_t) * 8 - depth));
    }

    int get_tid() const
    {
        return thread_id % thread_num;
    }

    atomic<DState *> table;
    vector<Operation> help;
    atomic_size_t op_seq_num{0};

    const unsigned thread_num;
};