#include "wf_hashtable.h"

WF_HashTable<int, int> table{1};

int main()
{
    table.insert(1, 2);
}