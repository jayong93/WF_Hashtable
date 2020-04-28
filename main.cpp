#include <iostream>
#include <chrono>
#include <thread>
#include "wf_hashtable.h"

using namespace std;
using namespace chrono;

unsigned long fastrand(void)
{ //period 2^96-1
    static thread_local unsigned long x = 123456789, y = 362436069, z = 521288629;
    unsigned long t;
    x ^= x << 16;
    x ^= x >> 5;
    x ^= x << 1;

    t = x;
    x = y;
    y = z;
    z = t ^ x ^ y;

    return z;
}

constexpr unsigned NUM_TEST = 4'000'000;
constexpr unsigned RANGE = 1'000;

using HashTable = WF_HashTable<unsigned, unsigned>;

void benchmark(unsigned num_thread, HashTable *table)
{
    for (int i = 0; i < NUM_TEST / num_thread; ++i)
    {
        //	if (0 == i % 100000) cout << ".";
        switch (fastrand() % 3)
        {
        case 0:
            table->insert(fastrand() % RANGE, fastrand());
            break;
        case 1:
            table->remove(fastrand() % RANGE);
            break;
        case 2:
            table->lookup(fastrand() % RANGE);
            break;
        default:
            printf("Unknown Command!\n");
            exit(-1);
        }
#ifdef DEBUG
        if (i % 500 == 0)
            printf("Thread #%d run operation #%d\n", thread_id, i);
#endif
    }
}

int main(int argc, char* argv[])
{
    for (unsigned num_thread = 1; num_thread <= 32; num_thread *= 2)
    {
        HashTable table{num_thread};

        vector<thread> worker;
        auto start_t = high_resolution_clock::now();
        for (unsigned i = 0; i < num_thread; ++i)
            worker.emplace_back(benchmark, num_thread, &table);
        for (auto &th : worker)
            th.join();
        auto du = high_resolution_clock::now() - start_t;

        table.dump();

        printf("%d Threads, Time=%ld ms\n", num_thread, duration_cast<milliseconds>(du).count());
        fflush(NULL);
    }
}