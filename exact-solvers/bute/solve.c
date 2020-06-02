#include "bitset.h"

#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define BUFFERSIZE 1024

int m = 0;

long tmp_counter = 0;

int tmpx = 0;

setword allmask[64];

//https://stackoverflow.com/a/10380191/3347737
#define PASTE_HELPER(a,b) a ## b
#define PASTE(a,b) PASTE_HELPER(a,b)

// If you use these macros, don't modify bitset while iterating over it!
#define FOR_EACH_IN_BITSET_HELPER(v, bitset, i, sw, x) \
           for (int i=0;i<m;i++) {setword sw=bitset[i]; while (sw) {int x; TAKEBIT(x, sw); int v=i*WORDSIZE+x;
#define FOR_EACH_IN_BITSET(v, bitset) \
           FOR_EACH_IN_BITSET_HELPER(v, bitset, PASTE(i,__LINE__), PASTE(sw,__LINE__), PASTE(x,__LINE__))
#define FOR_EACH_IN_BITSET_INTERSECTION_HELPER(v, bitset1, bitset2, i, sw, x) \
           for (int i=0;i<m;i++) {setword sw=bitset1[i] & bitset2[i]; while (sw) {int x; TAKEBIT(x, sw); int v=i*WORDSIZE+x;
#define FOR_EACH_IN_BITSET_INTERSECTION(v, bitset1, bitset2) \
           FOR_EACH_IN_BITSET_INTERSECTION_HELPER(v, bitset1, bitset2, PASTE(i,__LINE__), PASTE(sw,__LINE__), PASTE(x,__LINE__))
#define END_FOR_EACH_IN_BITSET }}

void set_first_k_bits(setword *bitset, int k)
{
    int wordnum = 0;
    while (k > 63) {
        bitset[wordnum] = ~0ull;
        ++wordnum;
        k -= 64;
    }
    if (k) {
        bitset[wordnum] = allmask[k];
    }
}

void bitset_intersect_with(setword *vv, setword const *ww)
{
    for (int i=0; i<m; i++)
        vv[i] &= ww[i];
}

int popcount_of_set_difference(setword const *vv, setword const *ww)
{
    int count = 0;
    for (int i=0; i<m; i++)
        count += POPCOUNT(vv[i] & ~ww[i]);
    return count;
}

bool intersection_is_empty(setword *vv, setword *ww)
{
    for (int i=0; i<m; i++)
        if (vv[i] & ww[i])
            return false;
    return true;
}

/* We have a free-list of bitsets */

struct Bitset
{
    struct Bitset *next;
    setword bitset[];
};

struct Bitset *bitset_free_list_head = NULL;

struct Bitset *get_Bitset()
{
    if (bitset_free_list_head == NULL) {
        struct Bitset *b = malloc(sizeof(struct Bitset) + m * sizeof(setword));
        if (b == NULL)
            exit(1);
        b->next = NULL;
        bitset_free_list_head = b;
    }
    struct Bitset *b = bitset_free_list_head;
    bitset_free_list_head = b->next;
    return b;
}

setword *get_bitset()
{
    return get_Bitset()->bitset;
}

setword *get_empty_bitset()
{
    setword *b = get_bitset();
    for (int i=0; i<m; i++)
        b[i] = 0;
    return b;
}

setword *get_copy_of_bitset(setword const *vv)
{
    setword *b = get_bitset();
    for (int i=0; i<m; i++)
        b[i] = vv[i];
    return b;
}

void free_Bitset(struct Bitset *b)
{
    b->next = bitset_free_list_head;
    bitset_free_list_head = b;
}

void free_bitset(setword *bitset)
{
    struct Bitset *b = (struct Bitset *)((char *) bitset - offsetof(struct Bitset, bitset));
    free_Bitset(b);
}

void free_Bitsets(struct Bitset *b)
{
    while (b) {
        struct Bitset *next_to_free = b->next;
        free_Bitset(b);
        b = next_to_free;
    }
}

void deallocate_Bitsets()
{
    while (bitset_free_list_head) {
        struct Bitset *next_to_free = bitset_free_list_head->next;
        free(bitset_free_list_head);
        bitset_free_list_head = next_to_free;
    }
}

/*************************************/

bool bitsets_are_equal(setword *vv, setword *ww)
{
    for (int i=0; i<m; i++)
        if (vv[i] != ww[i])
            return false;
    return true;
}

bool bitset_is_superset(setword *vv, setword *ww)
{
    for (int i=0; i<m; i++)
        if (ww[i] & ~vv[i])
            return false;
    return true;
}

bool bitset_union_is_superset(setword *vv, setword *uu, setword *ww)
{
    for (int i=0; i<m; i++)
        if (ww[i] & ~(vv[i] | uu[i]))
            return false;
    return true;
}

/** Hash map *************************/

struct hash_chain_element
{
    int val;
    struct hash_chain_element *next;
    setword key[];
};

struct hash_set
{
    int M;
    int sz;
    struct hash_chain_element **chain_heads;
};

void hash_init(struct hash_set *s)
{
    s->M = 1;
    s->sz = 0;
    s->chain_heads = calloc(s->M, sizeof *s->chain_heads);
}

// Based on https://gist.github.com/badboy/6267743
unsigned hash6432shift(setword key)
{
    key = (~key) + (key << 18); // key = (key << 18) - key - 1;
    key = key ^ (key >> 31);
    key = (key + (key << 2)) + (key << 4);
    key = key ^ (key >> 11);
    key = key + (key << 6);
    key = key ^ (key >> 22);
    return (unsigned) key;
}

unsigned hash(setword *x)
{
    unsigned result = 0;
    for (int i=0; i<m; i++) {
        result ^= hash6432shift(x[i]);
    }
    return result;
}

void hash_grow(struct hash_set *s)
{
//    printf("growing from %d to %d\n", s->M, s->M * 2);
    // grow the table
    int new_M = s->M * 2;

    struct hash_chain_element **new_chain_heads = calloc(new_M, sizeof new_chain_heads);
    // move the chain elements to the new chains
    for (int i=0; i<s->M; i++) {
        struct hash_chain_element *p = s->chain_heads[i];
        while (p) {
            struct hash_chain_element *next_in_old_list = p->next;
            unsigned h = hash(p->key) % new_M;
            p->next = new_chain_heads[h];
            new_chain_heads[h] = p;
            p = next_in_old_list;
        }
    }
    free(s->chain_heads);
    s->chain_heads = new_chain_heads;
    s->M = new_M;
}

// Assumption: key is not in s already
void hash_add(struct hash_set *s, setword * key, int val)
{
//    printf("adding\n");
//    printf("HASH %d\n", (int)hash(key));
    unsigned h = hash(key) % s->M;
    struct hash_chain_element *elem = malloc(sizeof *elem + m * sizeof(setword));
    for (int k=0; k<m; k++)
        elem->key[k] = key[k];
    elem->val = val;
    elem->next = s->chain_heads[h];
    s->chain_heads[h] = elem;
    ++s->sz;
    
    if (s->sz > (s->M + 1) / 2) {
        hash_grow(s);
    }
}

// Assumption: key is in s
void hash_delete(struct hash_set *s, setword *key)
{
    unsigned h = hash(key) % s->M;
    struct hash_chain_element **p = &s->chain_heads[h];
    while (!bitsets_are_equal((*p)->key, key)) {
        p = &(*p)->next;
    }
    // p points to a pointer to the element containing key
    struct hash_chain_element *new_next = (*p)->next;
    free(*p);
    *p = new_next;
    --s->sz;
}

bool hash_get_val(struct hash_set *s, setword *key, int *val)
{
    unsigned h = hash(key) % s->M;
    struct hash_chain_element *p = s->chain_heads[h];
    while (p) {
        if (bitsets_are_equal(p->key, key)) {
            *val = p->val;
            return true;
        }
        p = p->next;
    }
    return false;
}

bool hash_iselement(struct hash_set *s, setword *key)
{
    int junk;
    return hash_get_val(s, key, &junk);
}

void hash_add_or_update(struct hash_set *s, setword * key, int val)
{
    unsigned h = hash(key) % s->M;
    struct hash_chain_element *p = s->chain_heads[h];
    while (p) {
        if (bitsets_are_equal(p->key, key)) {
            p->val = val;
            return;
        }
        p = p->next;
    }

    struct hash_chain_element *elem = malloc(sizeof *elem + m * sizeof(setword));
    for (int k=0; k<m; k++)
        elem->key[k] = key[k];
    elem->val = val;
    elem->next = s->chain_heads[h];
    s->chain_heads[h] = elem;
    ++s->sz;
    
    if (s->sz > (s->M + 1) / 2) {
        hash_grow(s);
    }
}

void hash_print_all(struct hash_set *s)
{
    for (int i=0; i<s->M; i++) {
        printf("%d:  ", i);
        struct hash_chain_element *p = s->chain_heads[i];
        while (p) {
            for (int i=0; i<m * 64; i++) {
                printf("%d", ISELEMENT(p->key, i));
            }
            printf(",%d ", p->val);
            p = p->next;
        }
        printf("\n");
    }
    printf("\n");
}

setword ** hash_set_to_list(struct hash_set *s)
{
    setword **retval = malloc(s->sz * sizeof *retval);
    int j = 0;
    for (int i=0; i<s->M; i++) {
        struct hash_chain_element *p = s->chain_heads[i];
        while (p) {
            retval[j] = get_bitset();
            for (int k=0; k<m; k++) {
                retval[j][k] = p->key[k];
            }
            j++;
            p = p->next;
        }
    }
    return retval;
}

void hash_destroy(struct hash_set *s)
{
    for (int i=0; i<s->M; i++) {
        struct hash_chain_element *p = s->chain_heads[i];
        while (p) {
            struct hash_chain_element *next_p = p->next;
            free(p);
            p = next_p;
        }
    }
    free(s->chain_heads);
}

/** Trie *****************************/

// This data structure is largely based on https://stackoverflow.com/a/6514445/3347737

// SMALL_ARR_LEN must be a power of 2
#define SMALL_ARR_LEN 2

#define SMALL_BITSET_LEN 2

struct TrieNode
{
    int *successor_node_num;

    // The intersection of sets in the subtree below this node.
    // To simplify the code, there is a special case: initially, for the root node,
    // this contains the set of all vertices.
    setword *subtree_intersection;

    setword *subtree_intersection_of_aux_bitsets;

    // avoid some mallocations
    int small_arr[SMALL_ARR_LEN];
    setword small_bitset[SMALL_BITSET_LEN];
    setword small_aux_bitset[SMALL_BITSET_LEN];

    int key;
    int successor_len;
    int val;
    int num_vals_in_subtrie;
    int val_in_subtrie;    // only used if num_vals_in_subtrie is 1
};

struct Trie
{
    struct TrieNode *nodes;
    struct TrieNode root;
    int nodes_len;
    int graph_n;
};

void trie_init(struct Trie *trie, int n)
{
    trie->graph_n = n;
    trie->nodes_len = 0;
    trie->nodes = NULL;

    trie->root.key = -1;
    trie->root.val = -1;
    trie->root.successor_len = 0;
    trie->root.subtree_intersection = m <= SMALL_BITSET_LEN ? trie->root.small_bitset : get_bitset();
    trie->root.subtree_intersection_of_aux_bitsets = m <= SMALL_BITSET_LEN ? trie->root.small_aux_bitset : get_bitset();
    set_first_k_bits(trie->root.subtree_intersection, trie->graph_n);
    set_first_k_bits(trie->root.subtree_intersection_of_aux_bitsets, trie->graph_n);
    trie->root.num_vals_in_subtrie = 0;
}

void trie_destroy(struct Trie *trie)
{
    for (int i=0; i<trie->nodes_len; i++) {
        struct TrieNode *node = &trie->nodes[i];
        if (node->successor_len > SMALL_ARR_LEN) {
            free(node->successor_node_num);
        }
        if (m > SMALL_BITSET_LEN) {
            free_bitset(node->subtree_intersection);
            free_bitset(node->subtree_intersection_of_aux_bitsets);
        }
    }
    if (trie->root.successor_len > SMALL_ARR_LEN) {
        free(trie->root.successor_node_num);
    }
    if (m > SMALL_BITSET_LEN) {
        free_bitset(trie->root.subtree_intersection);
        free_bitset(trie->root.subtree_intersection_of_aux_bitsets);
    }
    free(trie->nodes);
}

void trie_grow_if_necessary(struct Trie *trie)
{
    if (trie->nodes_len == 0) {
        trie->nodes = malloc(1 * sizeof *trie->nodes);
    } else if (__builtin_popcount(trie->nodes_len) == 1) {
        trie->nodes = realloc(trie->nodes, trie->nodes_len * 2 * sizeof *trie->nodes);
        for (int i=0; i<trie->nodes_len; i++) {
            if (trie->nodes[i].successor_len <= SMALL_ARR_LEN) {
                trie->nodes[i].successor_node_num = trie->nodes[i].small_arr;
            }
            if (m <= SMALL_BITSET_LEN) {
                trie->nodes[i].subtree_intersection = trie->nodes[i].small_bitset;
                trie->nodes[i].subtree_intersection_of_aux_bitsets = trie->nodes[i].small_aux_bitset;
            }
        }
    }
}

void trie_node_grow_if_necessary(struct TrieNode *node)
{
    if (node->successor_len < SMALL_ARR_LEN) {
        node->successor_node_num = node->small_arr;
    } else if (node->successor_len == SMALL_ARR_LEN) {
        node->successor_node_num = malloc(SMALL_ARR_LEN * 2 * sizeof *node->successor_node_num);
        for (int i=0; i<SMALL_ARR_LEN; i++) {
            node->successor_node_num[i] = node->small_arr[i];
        }
    } else if (__builtin_popcount(node->successor_len) == 1) {
        node->successor_node_num = realloc(node->successor_node_num, node->successor_len * 2 * sizeof *node->successor_node_num);
    }
}

int trie_get_successor_node_num(struct Trie *trie, struct TrieNode *node, int key)
{
    for (int i=0; i<node->successor_len; i++) {
        int succ_node_num = node->successor_node_num[i];
        struct TrieNode *succ_node = &trie->nodes[succ_node_num];
        if (succ_node->key == key) {
            return succ_node_num;
        }
    }
    return -1;
}

struct TrieNode * trie_add_successor(struct Trie *trie, struct TrieNode *node, int key)
{
    trie_node_grow_if_necessary(node);
    node->successor_node_num[node->successor_len] = trie->nodes_len;
    ++node->successor_len;
//    printf("! %d %d\n", node->successor_len, node==&trie->root);

    trie_grow_if_necessary(trie);
    struct TrieNode *succ = &trie->nodes[trie->nodes_len];
    ++trie->nodes_len;

    succ->key = key; 
    succ->val = -1;
    succ->successor_len = 0;
    succ->num_vals_in_subtrie = 0;

    return succ;
}

void trie_get_all_almost_subsets_helper(struct Trie *trie, struct TrieNode *node, setword *set,
        setword *aux_set, int num_additions_permitted, int *arr_out, int *arr_out_len)
{
//    ++tmp_counter;
    if (node->val != -1) {
        arr_out[(*arr_out_len)++] = node->val;
    }
    for (int i=0; i<node->successor_len; i++) {
        int succ_node_num = node->successor_node_num[i];
        struct TrieNode *succ = &trie->nodes[succ_node_num];
        if (popcount_of_set_difference(succ->subtree_intersection, set) <= num_additions_permitted &&
                intersection_is_empty(aux_set, succ->subtree_intersection_of_aux_bitsets)) {
            if (succ->num_vals_in_subtrie == 1) {
                // this saves the work of traversing all the way down to a leaf node of the trie
                arr_out[(*arr_out_len)++] = succ->val_in_subtrie;
                continue;
            } else {
                trie_get_all_almost_subsets_helper(trie, succ, set, aux_set, num_additions_permitted,
                        arr_out, arr_out_len);
            }
        }
    }
}

void trie_get_all_almost_subsets(struct Trie *trie, setword *set, setword *aux_set, int num_additions_permitted, int *arr_out, int *arr_out_len)
{
    *arr_out_len = 0;
    trie_get_all_almost_subsets_helper(trie, &trie->root, set, aux_set, num_additions_permitted, arr_out, arr_out_len);
}

// key is an array terminated by -1
void trie_add_key_val(struct Trie *trie, int *key, setword *key_bitset, int val)
{
    struct TrieNode *node = &trie->root;
    bitset_intersect_with(node->subtree_intersection, key_bitset);
    ++node->num_vals_in_subtrie;
    node->val_in_subtrie = val;
    while (*key != -1) {
//        printf("dbg key %d\n", *key);
        int succ_node_num = trie_get_successor_node_num(trie, node, *key);
//        printf("dbg succ node num %d\n", succ_node_num);
        if (succ_node_num != -1) {
            node = &trie->nodes[succ_node_num];
        } else {
            node = trie_add_successor(trie, node, *key);
            node->subtree_intersection = m <= SMALL_BITSET_LEN ? node->small_bitset : get_bitset();
            node->subtree_intersection_of_aux_bitsets = m <= SMALL_BITSET_LEN ? node->small_aux_bitset : get_bitset();
            set_first_k_bits(node->subtree_intersection, trie->graph_n);
            set_first_k_bits(node->subtree_intersection_of_aux_bitsets, trie->graph_n);
        }
        ++node->num_vals_in_subtrie;
        node->val_in_subtrie = val;
        bitset_intersect_with(node->subtree_intersection, key_bitset);
        ++key;
//        printf("node count %d\n", trie->nodes_len);
    }
    node->val = val;
}

void trie_add_an_aux_bitset(struct Trie *trie, int *key, setword *aux_bitset)
{
    struct TrieNode *node = &trie->root;
    bitset_intersect_with(node->subtree_intersection_of_aux_bitsets, aux_bitset);
    while (*key != -1) {
//        printf("dbg key %d\n", *key);
        int succ_node_num = trie_get_successor_node_num(trie, node, *key);
//        printf("dbg succ node num %d\n", succ_node_num);
        if (succ_node_num != -1) {
            node = &trie->nodes[succ_node_num];
        } else {
            printf("????\n");
            exit(1);
        }
        bitset_intersect_with(node->subtree_intersection_of_aux_bitsets, aux_bitset);
        ++key;
//        printf("node count %d\n", trie->nodes_len);
    }
}

/*************************************/

struct Dom
{
    setword **vv_dominated_by;
    setword **vv_that_dominate;
    setword **adj_vv_dominated_by;
    setword **adj_vv_that_dominate;
};

/*************************************/

void bitset_union(setword *dest, setword const *src1, setword const *src2)
{
    for (int i=0; i<m; i++)
        dest[i] = src1[i] | src2[i];
}

void bitset_addall(setword *vv, setword const *ww)
{
    for (int i=0; i<m; i++)
        vv[i] |= ww[i];
}

void bitset_removeall(setword *vv, setword const *ww)
{
    for (int i=0; i<m; i++)
        vv[i] &= ~ww[i];
}

int bitset_compare(setword const *vv, setword const *ww)
{
    for (int i=0; i<m; i++) {
        if (vv[i] != ww[i]) {
            return vv[i] < ww[i] ? -1 : 1;
        }
    }
    return 0;
}

void clear_bitset(setword *vv)
{
    for (int i=0; i<m; i++)
        vv[i] = 0;
}

bool isempty(setword *vv)
{
    for (int i=0; i<m; i++)
        if (vv[i])
            return false;
    return true;
}

int popcount(setword const *vv)
{
    int count = 0;
    for (int i=0; i<m; i++)
        count += POPCOUNT(vv[i]);
    return count;
}

int popcount_of_union(setword const *vv, setword const *ww)
{
    int count = 0;
    for (int i=0; i<m; i++)
        count += POPCOUNT(vv[i] | ww[i]);
    return count;
}

int firstelement(setword const *vv)
{
    for (int i=0; i<m; i++)
        if (vv[i])
            return FIRSTBITNZ(vv[i]) + i * WORDSIZE;
    return -1;
}

// Returns a pointer to the first bitset in a linked list
struct Bitset *make_connected_components(setword *vv, graph *g)
{
    struct Bitset *retval = NULL;
    setword *visited = get_empty_bitset();
    setword *vv_in_prev_components = get_empty_bitset();
    setword *frontier = get_empty_bitset();
    for (int j=0; j<m; j++) {
        int x;
        while (-1 != (x = FIRSTBIT(vv[j] & ~visited[j]))) {
            int v = x + j * WORDSIZE;
            clear_bitset(frontier);
            ADDELEMENT(frontier, v);
            bool frontier_empty = false;
            while (!frontier_empty) {
                int u = firstelement(frontier);
                DELELEMENT(frontier, u);
                ADDELEMENT(visited, u);
                graph *graphrow = GRAPHROW(g, u, m);
                frontier_empty = true;
                for (int k=0; k<m; k++) {
                    frontier[k] |= graphrow[k] & ~visited[k] & vv[k];
                    frontier_empty &= frontier[k] == 0;
                }
            }

            struct Bitset *bitset = get_Bitset();
            bitset->next = retval;
            retval = bitset;
            setword *component = bitset->bitset;
            for (int k=0; k<m; k++)
                component[k] = visited[k] & ~vv_in_prev_components[k];

            for (int k=0; k<m; k++)
                vv_in_prev_components[k] |= visited[k];
        }
    }

    free_bitset(frontier);
    free_bitset(vv_in_prev_components);
    free_bitset(visited);
    return retval;
}

struct VtxInfo
{
    int v;
    int degree;
};

void find_adjacent_vv(setword *s, graph *g, setword *adj_vv)
{
    clear_bitset(adj_vv);
    FOR_EACH_IN_BITSET(v, s)
        for (int k=0; k<m; k++) {
            adj_vv[k] |= GRAPHROW(g, v, m)[k];
        }
    END_FOR_EACH_IN_BITSET
    for (int k=0; k<m; k++) {
        adj_vv[k] &= ~s[k];
    }
}

struct SetAndNeighbourhood
{
    setword *set;
    setword *nd;
    int sorted_position;
};

int cmp_nd_popcount_desc(const void *a, const void *b) {
    const struct SetAndNeighbourhood sa = *(const struct SetAndNeighbourhood *) a;
    const struct SetAndNeighbourhood sb = *(const struct SetAndNeighbourhood *) b;
    if (sa.sorted_position != -1) {
        return sa.sorted_position - sb.sorted_position;
    }
    int pca = popcount(sa.nd);
    int pcb = popcount(sb.nd);
    if (pca != pcb) {
        return pca > pcb ? -1 : 1;
    }
    int comp = bitset_compare(sa.nd, sb.nd);
    if (comp != 0)
        return comp;
    pca = popcount(sa.set);
    pcb = popcount(sb.set);
    if (pca != pcb) {
        return pca > pcb ? -1 : 1;
    }
    return bitset_compare(sa.set, sb.set);
}

// if filtered_leafysets_len is small, use a simple filtering algorithm to
// avoid the overhead of the trie
#define MIN_LEN_FOR_TRIE 50

void make_leafysets_helper(struct SetAndNeighbourhood *filtered_leafysets, int filtered_leafysets_len, struct hash_set *leafysets_as_set,
        graph *g, int n, struct Dom *dom,
        setword *possible_leafyset_roots, setword *union_of_subtrees, setword *nd_of_union_of_subtrees, int root_depth, struct hash_set *set_root, struct hash_set *new_leafysets_hash_set)
{
    ++tmp_counter;

    if (!filtered_leafysets_len) {
        return;
    }
    struct Trie trie;
    if (filtered_leafysets_len >= MIN_LEN_FOR_TRIE)
        trie_init(&trie, n);
    int *almost_subset_end_positions = malloc(filtered_leafysets_len * sizeof *almost_subset_end_positions);
    bool *leafyset_is_first_of_equal_nd_run = calloc(filtered_leafysets_len, sizeof *leafyset_is_first_of_equal_nd_run);

    int *nd_arr = malloc((n+1) * sizeof *nd_arr);

    struct SetAndNeighbourhood *further_filtered_leafysets = malloc(filtered_leafysets_len * sizeof *further_filtered_leafysets);

    for (int i=filtered_leafysets_len-1; i>=0; i--) {
        setword *new_big_union = get_empty_bitset();
        setword *s = filtered_leafysets[i].set;
        setword *new_possible_leafyset_roots = get_copy_of_bitset(possible_leafyset_roots);
        bitset_intersect_with(new_possible_leafyset_roots, filtered_leafysets[i].nd);
        setword *new_union_of_subtrees = get_copy_of_bitset(union_of_subtrees);
        bitset_addall(new_union_of_subtrees, s);

        setword *nd_of_new_union_of_subtrees = get_copy_of_bitset(nd_of_union_of_subtrees);
        bitset_addall(nd_of_new_union_of_subtrees, filtered_leafysets[i].nd);
        bitset_removeall(nd_of_new_union_of_subtrees, new_union_of_subtrees);

        FOR_EACH_IN_BITSET(w, new_possible_leafyset_roots)
            setword *adj_vv = get_copy_of_bitset(nd_of_new_union_of_subtrees);
            bitset_addall(adj_vv, GRAPHROW(g, w, m));
            bitset_removeall(adj_vv, new_union_of_subtrees);
            if (popcount(adj_vv) <= root_depth) {
                setword *leafyset = get_copy_of_bitset(new_union_of_subtrees);
                ADDELEMENT(leafyset, w);
                if (intersection_is_empty(dom->vv_dominated_by[w], adj_vv) &&
                        intersection_is_empty(dom->vv_that_dominate[w], leafyset) &&
                        !hash_iselement(set_root, leafyset)) {
                    hash_add(new_leafysets_hash_set, leafyset, 1);
                    hash_add(set_root, leafyset, w);
                }
                free_bitset(leafyset);
            }
            free_bitset(adj_vv);
        END_FOR_EACH_IN_BITSET

        setword *new_union_of_subtrees_and_nd = get_copy_of_bitset(new_union_of_subtrees);
        bitset_addall(new_union_of_subtrees_and_nd, nd_of_new_union_of_subtrees);
        int further_filtered_leafysets_len = 0;

        if (filtered_leafysets_len >= MIN_LEN_FOR_TRIE) {
            int almost_subset_end_positions_len;
            trie_get_all_almost_subsets(&trie, filtered_leafysets[i].nd, new_union_of_subtrees_and_nd, root_depth - popcount(filtered_leafysets[i].nd),
                    almost_subset_end_positions, &almost_subset_end_positions_len);
            if (root_depth == popcount(filtered_leafysets[i].nd)) {
                int it = i + 1;
                while (it < filtered_leafysets_len && bitsets_are_equal(filtered_leafysets[i].nd, filtered_leafysets[it].nd)) {
                    it++;
                }
                if (it > i + 1) {
                    almost_subset_end_positions[almost_subset_end_positions_len++] = it - 1;
                }
            }
            for (int j=0; j<almost_subset_end_positions_len; j++) {
                int iter = almost_subset_end_positions[j];
                struct SetAndNeighbourhood fl = filtered_leafysets[iter];
                if (intersection_is_empty(fl.nd, new_possible_leafyset_roots) ||
                        popcount_of_union(nd_of_new_union_of_subtrees, fl.nd) > root_depth) {
                    continue;
                }
                for ( ; iter > i; iter--) {
                    struct SetAndNeighbourhood fl = filtered_leafysets[iter];
                    if (intersection_is_empty(new_union_of_subtrees_and_nd, fl.set)) {
                        further_filtered_leafysets[further_filtered_leafysets_len++] = fl;
                        bitset_addall(new_big_union, fl.set);
                    }
                    if (leafyset_is_first_of_equal_nd_run[iter]) {
                        break;
                    }
                }
            }
        } else {
            for (int j=i+1; j<filtered_leafysets_len; j++) {
                struct SetAndNeighbourhood fl = filtered_leafysets[j];
                if (intersection_is_empty(fl.nd, new_possible_leafyset_roots))
                    continue;
                if (popcount_of_union(nd_of_new_union_of_subtrees, fl.nd) > root_depth)
                    continue;
                if (!intersection_is_empty(new_union_of_subtrees_and_nd, fl.set))
                    continue;
                further_filtered_leafysets[further_filtered_leafysets_len++] = fl;
                bitset_addall(new_big_union, fl.set);
            }
        }

        qsort(further_filtered_leafysets, further_filtered_leafysets_len, sizeof *further_filtered_leafysets, cmp_nd_popcount_desc);

        setword *adj_vv = get_bitset();
        FOR_EACH_IN_BITSET(v, new_possible_leafyset_roots)
            bitset_union(adj_vv, nd_of_new_union_of_subtrees, GRAPHROW(g,v,m));
            bitset_removeall(adj_vv, new_union_of_subtrees);
            DELELEMENT(adj_vv, v);
            bitset_removeall(adj_vv, new_big_union);
            if (popcount(adj_vv) >= root_depth || !bitset_union_is_superset(new_big_union, new_union_of_subtrees, dom->adj_vv_dominated_by[v])) {
                DELELEMENT(new_possible_leafyset_roots, v);
            }
        END_FOR_EACH_IN_BITSET

        if (!isempty(new_possible_leafyset_roots)) {
            make_leafysets_helper(further_filtered_leafysets, further_filtered_leafysets_len, leafysets_as_set,
                    g, n, dom, new_possible_leafyset_roots, new_union_of_subtrees, nd_of_new_union_of_subtrees, root_depth, set_root, new_leafysets_hash_set);
        }

        free_bitset(adj_vv);
        free_bitset(new_union_of_subtrees_and_nd);

        free_bitset(nd_of_new_union_of_subtrees);
        free_bitset(new_possible_leafyset_roots);

        free_bitset(new_union_of_subtrees);
        free_bitset(new_big_union);

        if (i == 0 || !bitsets_are_equal(filtered_leafysets[i].nd, filtered_leafysets[i-1].nd)) {
            leafyset_is_first_of_equal_nd_run[i] = true;
        }
        if (filtered_leafysets_len >= MIN_LEN_FOR_TRIE) {
            if (root_depth > popcount(filtered_leafysets[i].nd)) {
                if (i == filtered_leafysets_len-1 || !bitsets_are_equal(filtered_leafysets[i].nd, filtered_leafysets[i+1].nd)) {
                    int pos = 0;
                    FOR_EACH_IN_BITSET(w, filtered_leafysets[i].nd)
                        nd_arr[pos++] = w;
                    END_FOR_EACH_IN_BITSET
                    nd_arr[pos] = -1;
                    trie_add_key_val(&trie, nd_arr, filtered_leafysets[i].nd, i);
                }
                // There's no need to consider a subtrie all of whose keys contain a vertex v that is
                // in the new union of sets or their neighbourhood
                trie_add_an_aux_bitset(&trie, nd_arr, filtered_leafysets[i].set);
            }
        }
    }
    free(further_filtered_leafysets);
    if (filtered_leafysets_len >= MIN_LEN_FOR_TRIE)
        trie_destroy(&trie);
    free(almost_subset_end_positions);
    free(leafyset_is_first_of_equal_nd_run);
    free(nd_arr);
}

int *vtx_num_appearances_in_leafysets;

setword **make_leafysets(setword **leafysets, int leafysets_len, graph *g, int n,
        struct Dom *dom,
        int root_depth, struct hash_set *set_root, int *new_leafysets_len)
{
    struct hash_set new_leafysets_hash_set;
    hash_init(&new_leafysets_hash_set);
    struct hash_set leafysets_as_set;
    hash_init(&leafysets_as_set);
    struct SetAndNeighbourhood *leafysets_and_nds = malloc(leafysets_len * sizeof *leafysets_and_nds);
    for (int i=0; i<leafysets_len; i++) {
        hash_add(&leafysets_as_set, leafysets[i], 1);
        leafysets_and_nds[i].set = leafysets[i];
        leafysets_and_nds[i].nd = get_bitset();
        find_adjacent_vv(leafysets[i], g, leafysets_and_nds[i].nd);
        leafysets_and_nds[i].sorted_position = -1;
    }

    qsort(leafysets_and_nds, leafysets_len, sizeof *leafysets_and_nds, cmp_nd_popcount_desc);
    for (int i=0; i<leafysets_len; i++) {
        leafysets_and_nds[i].sorted_position = i;
    }

    for (int v=0; v<n; v++) {
        setword *single_vtx_leafyset = get_empty_bitset();
        ADDELEMENT(single_vtx_leafyset, v);
        if (popcount(GRAPHROW(g, v, m)) < root_depth && isempty(dom->adj_vv_dominated_by[v])
                && !hash_iselement(set_root, single_vtx_leafyset)) {
            hash_add(&new_leafysets_hash_set, single_vtx_leafyset, 1);
            hash_add(set_root, single_vtx_leafyset, v);
        }
        free_bitset(single_vtx_leafyset);
    }

    setword *empty_set = get_empty_bitset();
    setword *full_set = get_bitset();
    set_first_k_bits(full_set, n);
    struct SetAndNeighbourhood *filtered_leafysets = malloc(leafysets_len * sizeof *filtered_leafysets);
    int filtered_leafysets_len = 0;
    for (int i=0; i<leafysets_len; i++) {
        filtered_leafysets[filtered_leafysets_len++] = leafysets_and_nds[i];
    }

    make_leafysets_helper(filtered_leafysets, filtered_leafysets_len, &leafysets_as_set,
            g, n, dom, full_set, empty_set, empty_set, root_depth, set_root, &new_leafysets_hash_set);
    free(filtered_leafysets);
    free_bitset(empty_set);
    free_bitset(full_set);

    for (int i=0; i<leafysets_len; i++) {
        free_bitset(leafysets_and_nds[i].nd);
    }
    free(leafysets_and_nds);
    setword **retval = hash_set_to_list(&new_leafysets_hash_set);
    *new_leafysets_len = new_leafysets_hash_set.sz;
    hash_destroy(&new_leafysets_hash_set);
    hash_destroy(&leafysets_as_set);
    return retval;
}

int cmp_popcount_desc(const void *a, const void *b) {
    const setword *sa = *(const setword **) a;
    const setword *sb = *(const setword **) b;
    int pca = popcount(sa);
    int pcb = popcount(sb);
    if (pca < pcb)
        return 1;
    if (pca > pcb)
        return -1;
    return bitset_compare(sa, sb);
}

void add_parents(int *parent, graph *g, struct hash_set *set_root, setword *s, int parent_vertex)
{
    int v;
    if (!hash_get_val(set_root, s, &v)) {
        printf("Something went wrong.\n");
        exit(1);
    }
    parent[v] = parent_vertex;
    setword *vv_in_child_subtrees = get_copy_of_bitset(s);
    DELELEMENT(vv_in_child_subtrees, v);
    struct Bitset * components = make_connected_components(vv_in_child_subtrees, g);
    for (struct Bitset *component=components; component!=NULL; component=component->next) {
        add_parents(parent, g, set_root, component->bitset, v);
    }
    free_Bitsets(components);
    free_bitset(vv_in_child_subtrees);
}

bool solve(graph *g, int n, struct Dom *dom, int target, int *parent)
{
    bool retval = false;
    struct hash_set set_root;
    hash_init(&set_root);

    setword **leafysets = malloc(n * sizeof *leafysets);
    int leafysets_len = 0;

    for (int root_depth=target; root_depth>=1; root_depth--) {
//        printf("root depth %d\n", root_depth);
//        printf(" %d\n", leafysets_len);
        int new_leafysets_len = 0;
        setword **new_leafysets = make_leafysets(leafysets, leafysets_len, g, n, dom, root_depth, &set_root, &new_leafysets_len);
        if (new_leafysets_len == 0) {
            free(new_leafysets);
            break;
        }
        leafysets = realloc(leafysets, (leafysets_len + new_leafysets_len) * sizeof *leafysets);
        for(int i=0; i<new_leafysets_len; i++) {
            leafysets[leafysets_len + i] = new_leafysets[i];
        }
        leafysets_len = leafysets_len + new_leafysets_len;

        struct hash_set leafysets_as_set;
        hash_init(&leafysets_as_set);
        for (int i=0; i<leafysets_len; i++) {
            hash_add(&leafysets_as_set, leafysets[i], 1);
        }

        int k = 0;
        for (int i=0; i<leafysets_len; i++) {
            setword *adj_vv = get_bitset();
            find_adjacent_vv(leafysets[i], g, adj_vv);
            if (popcount(adj_vv) < root_depth) {
                if (!retval && popcount(leafysets[i]) + popcount(adj_vv) == n) {
                    retval = true;
                    int parent_vertex = -1;;
                    FOR_EACH_IN_BITSET(w, adj_vv)
                        parent[w] = parent_vertex;
                        parent_vertex = w;
                    END_FOR_EACH_IN_BITSET
                    add_parents(parent, g, &set_root, leafysets[i], parent_vertex);
                }
                leafysets[k++] = leafysets[i];
            } else {
                free_bitset(leafysets[i]);
            }
            free_bitset(adj_vv);
        }
        leafysets_len = k;
        qsort(leafysets, leafysets_len, sizeof *leafysets, cmp_popcount_desc);
        hash_destroy(&leafysets_as_set);
        free(new_leafysets);
        if (retval) {
            break;
        }
    }
    
    for (int i=0; i<leafysets_len; i++) {
        free_bitset(leafysets[i]);
    }
    free(leafysets);
    hash_destroy(&set_root);
    return retval;
}

int main(int argc, char *argv[])
{
    setword sw = 0;
    for (int i=0; i<64; i++) {
        allmask[i] = sw;
        sw |= BIT(i);
    }

    char s[BUFFERSIZE], s1[32], s2[32];
    int n, edge_count;
    int v, w;
    int num_edges_read = 0;
    graph *g = NULL;
    while (true) {
        if (fgets(s, BUFFERSIZE, stdin) == NULL)
            break;

        switch (s[0]) {
        case '\n':
            break;
        case 'c':
            break;
        case 'p':
            if(sscanf(s, "%s %s %d %d", s1, s2, &n, &edge_count) != 4)
                exit(1);
            m = SETWORDSNEEDED(n);
            g = calloc(n * m, sizeof(graph));
            break;
        default:
            if (sscanf(s, "%d %d", &v, &w) != 2)
                exit(1);
            if (v == w)
                continue;
            --v;
            --w;
            ADDONEEDGE(g, v, w, m);
            ++num_edges_read;
        }
    }

    struct Dom dom;
    dom.adj_vv_dominated_by = malloc(n * sizeof *dom.adj_vv_dominated_by);
    dom.adj_vv_that_dominate = malloc(n * sizeof *dom.adj_vv_that_dominate);
    dom.vv_dominated_by = malloc(n * sizeof *dom.vv_dominated_by);
    dom.vv_that_dominate = malloc(n * sizeof *dom.vv_that_dominate);
    for (int v=0; v<n; v++) {
        dom.adj_vv_dominated_by[v] = get_empty_bitset();
        dom.adj_vv_that_dominate[v] = get_empty_bitset();
        dom.vv_dominated_by[v] = get_empty_bitset();
        dom.vv_that_dominate[v] = get_empty_bitset();
    }
    for (int v=0; v<n; v++) {
        for (int w=0; w<n; w++) {
            if (w != v) {
                setword *nd_of_v_and_v_and_w = get_copy_of_bitset(GRAPHROW(g, v, m));
                ADDELEMENT(nd_of_v_and_v_and_w, v);
                ADDELEMENT(nd_of_v_and_v_and_w, w);
                setword *nd_of_w_and_v_and_w = get_copy_of_bitset(GRAPHROW(g, w, m));
                ADDELEMENT(nd_of_w_and_v_and_w, v);
                ADDELEMENT(nd_of_w_and_v_and_w, w);
                if (bitset_is_superset(nd_of_w_and_v_and_w, nd_of_v_and_v_and_w)) {
                    if (!bitsets_are_equal(nd_of_v_and_v_and_w, nd_of_w_and_v_and_w) || v < w) {
                        ADDELEMENT(dom.vv_dominated_by[w], v);
                        ADDELEMENT(dom.vv_that_dominate[v], w);
                        if (ISELEMENT(GRAPHROW(g, w, m), v)) {
                            ADDELEMENT(dom.adj_vv_dominated_by[w], v);
                            ADDELEMENT(dom.adj_vv_that_dominate[v], w);
                        }
                    }
                }
                free_bitset(nd_of_w_and_v_and_w);
                free_bitset(nd_of_v_and_v_and_w);
            }
        }
    }

    int *parent = malloc(n * sizeof *parent);
    for (int i=0; i<n; i++) {
        parent[i] = -1;
    }

    for (int target=0; target<=n; target++) {
//        printf("target %d\n", target);
        bool result = solve(g, n, &dom, target, parent);
        if (result) {
            printf("%d\n", target);
            for (int i=0; i<n; i++) {
                printf("%d\n", parent[i] + 1);
            }
            break;
        }
    }

    free(parent);

    for (int i=0; i<n; i++) {
        free_bitset(dom.adj_vv_dominated_by[i]);
        free_bitset(dom.adj_vv_that_dominate[i]);
        free_bitset(dom.vv_dominated_by[i]);
        free_bitset(dom.vv_that_dominate[i]);
    }
    free(dom.adj_vv_dominated_by);
    free(dom.adj_vv_that_dominate);
    free(dom.vv_dominated_by);
    free(dom.vv_that_dominate);
    free(g);
    deallocate_Bitsets();
}
