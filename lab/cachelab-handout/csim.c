/* 
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss. (I examined the trace,
 *  the largest request I saw was for 8 bytes).
 *  2. Instruction loads (I) are ignored, since we are interested in evaluating
 *  trans.c in terms of its data cache performance.
 *  3. data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus an possible eviction.
 *
 * The function printSummary() is given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * This is crucial for the driver to evaluate your work. 
 */
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include "cachelab.h"

//#define DEBUG_ON
#define ADDRESS_LENGTH 64

/* Type: Memory address */
typedef unsigned long long int mem_addr_t;

/* Type: Cache line
   LRU is a counter used to implement LRU replacement policy  */
typedef struct cache_line
{
    char valid;
    mem_addr_t tag;
    unsigned long long int lru;
} cache_line_t;

typedef cache_line_t *cache_set_t;
typedef cache_set_t *cache_t;

/* Globals set by command line args */
int verbosity = 0; /* print trace if set */
int s = 0;         /* set index bits */
int b = 0;         /* block offset bits */
int E = 0;         /* associativity */
char *trace_file = NULL;

/* Derived from command line args */
int S; /* number of sets */
int B; /* block size (bytes) */

/* Counters used to record cache statistics */
int miss_count = 0;
int hit_count = 0;
int eviction_count = 0;
unsigned long long int lru_counter = 1;

/* The cache we are simulating */
cache_t cache;
mem_addr_t set_index_mask;

/* 
 * initCache - Allocate memory, write 0's for valid and tag and LRU
 * also computes the set_index_mask
 */
void initCache()
{
    int i, j;
    cache = (cache_set_t *)malloc(sizeof(cache_set_t) * S);
    for (i = 0; i < S; i++)
    {
        cache[i] = (cache_line_t *)malloc(sizeof(cache_line_t) * E);
        for (j = 0; j < E; j++)
        {
            cache[i][j].valid = 0;
            cache[i][j].tag = 0;
            cache[i][j].lru = 0;
        }
    }

    /* Computes set index mask */
    set_index_mask = (mem_addr_t)(pow(2, s) - 1);
}

/* 
 * freeCache - free allocated memory
 */
void freeCache()
{
    int i;
    for (i = 0; i < S; i++)
    {
        free(cache[i]);
    }
    free(cache);
}

/* 
 * accessData - Access data at memory address addr.
 *   If it is already in cache, increast hit_count
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase eviction_count if a line is evicted.
 */
void accessData(mem_addr_t addr)
{
    int i;
    unsigned long long int eviction_lru = ULONG_MAX;
    unsigned int eviction_line = 0;
    mem_addr_t set_index = (addr >> b) & set_index_mask;
    mem_addr_t tag = addr >> (s + b);

    cache_set_t cache_set = cache[set_index];
    int hit_index = -1;     //命中行号
    int invalid_index = -1; //空闲行号
    /* 在set中的每一行查找 */
    for (i = 0; i < E; i++)
    {
        if (cache_set[i].valid)
        {
            cache_set[i].lru--; //无论是否命中，默认将LRU计数-1
            if (cache_set[i].lru < eviction_lru)
            {
                eviction_lru = cache_set[i].lru;
                eviction_line = i; //找出set中LRU计数最小值，若须替换则为替换行
            }
            if (cache_set[i].tag == tag)
            {
                /* 命中 */
                hit_index = i;
                // break; 此处不break，因为要将所有行的LRU计数默认-1
            }
        }
        else if (invalid_index == -1)
        {
            invalid_index = i; //如果有的话，记录下第一个空行
        }
    }
    /* 命中处理 */
    if (hit_index != -1)
    {
        if (verbosity)
        {
            printf("Hit! line:%d tag:%lld\n", hit_index, cache_set[hit_index].tag);
        }
        hit_count++;
        cache_set[hit_index].lru = ULONG_MAX; //LRU计数重置为最大值
        hit_index = -1;                       //重置命中行号为-1
    }
    /* 缺失处理 */
    else
    {
        miss_count++;
        /* 尝试找空位填入 */
        if (invalid_index != -1)
        {
            if (verbosity)
            {
                printf("Miss_Insert! line:%d tag:%lld\n", invalid_index, cache_set[invalid_index].tag);
            }
            cache_set[invalid_index].tag = tag;
            cache_set[invalid_index].lru = ULONG_MAX;
            cache_set[invalid_index].valid = 1;
            invalid_index = -1; //重置空闲行号为-1
        }
        /* 没有空位则替换 */
        else
        {
            if (verbosity)
            {
                printf("Miss_Evict! line:%d tag:%lld\n", eviction_line, cache_set[eviction_line].tag);
            }
            eviction_count++;
            cache_set[eviction_line].tag = tag;
            cache_set[eviction_line].lru = ULONG_MAX;
            eviction_lru = ULONG_MAX; //重置最小LRU计数为ULONG_MAX
        }
    }
}

/*
 * replayTrace - replays the given trace file against the cache 
 */
void replayTrace(char *trace_fn)
{
    char buf[1000];
    mem_addr_t addr = 0;
    unsigned int len = 0;
    FILE *trace_fp = fopen(trace_fn, "r");

    /* 跳过空格，读取行内容 */
    while (fscanf(trace_fp, " %s %llx,%u", buf, &addr, &len) != EOF)
    {
        if (verbosity)
        {
            printf("%s %llx,%u\n", buf, addr, len);
        }
        switch (buf[0])
        {
        case 'L':
            /* Load */
            accessData(addr);
            break;
        case 'S':
            /* Store */
            accessData(addr);
            break;
        case 'M':
            /* Modify */
            accessData(addr);
            accessData(addr);
            break;
        default:
            break;
        }
    }

    fclose(trace_fp);
}

/*
 * printUsage - Print usage info
 */
void printUsage(char *argv[])
{
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 * main - Main routine 
 */
int main(int argc, char *argv[])
{
    char c;

    while ((c = getopt(argc, argv, "s:E:b:t:vh")) != -1)
    {
        switch (c)
        {
        case 's':
            s = atoi(optarg);
            break;
        case 'E':
            E = atoi(optarg);
            break;
        case 'b':
            b = atoi(optarg);
            break;
        case 't':
            trace_file = optarg;
            break;
        case 'v':
            verbosity = 1;
            break;
        case 'h':
            printUsage(argv);
            exit(0);
        default:
            printUsage(argv);
            exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL)
    {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }

    /* Compute S, E and B from command line args */
    S = (unsigned int)pow(2, s);
    B = (unsigned int)pow(2, b);

    /* Initialize cache */
    initCache();

#ifdef DEBUG_ON
    printf("DEBUG: S:%u E:%u B:%u trace:%s\n", S, E, B, trace_file);
    printf("DEBUG: set_index_mask: %llu\n", set_index_mask);
#endif

    replayTrace(trace_file);

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics for the autograder */
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}
