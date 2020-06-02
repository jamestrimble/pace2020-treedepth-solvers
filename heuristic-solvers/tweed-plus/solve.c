#include "metis.h"
#include "struct.h"
#include "naurng.h"
#include "nauty.h"

#include <assert.h>
#include <limits.h>
#include <signal.h>
#include <stdbool.h>
#include <time.h>

#define BUFFERSIZE 1024
 
volatile sig_atomic_t tle = 0;
 
void term(int signum)
{
    tle = 1;
}

int *saved_parent;
int best;

int metis_seed = 0;   // this should be changed after each call to Metis

int m = 0;

int global_n = -1;

int *nd_len;
int **nd;

void print_decomp_and_exit_if_tle()
{
    if (tle) {
        printf("%d\n", best);
        for (int i=0; i<global_n; i++) {
            printf("%d\n", saved_parent[i] + 1);
        }
        exit(0);
    }
}

#define SMALLEST_GRAPH_FOR_SPLITTING .3
#define NUM_STARTING_POINTS 30
#define NUM_SPLITTING_POINTS 6
#define NUM_SUBGRAPHS (NUM_STARTING_POINTS * NUM_SPLITTING_POINTS)
double splitting_points[] = {.1, .15, .2, .25, .3, .4};

//https://stackoverflow.com/a/10380191/3347737
#define PASTE_HELPER(a,b) a ## b
#define PASTE(a,b) PASTE_HELPER(a,b)

// If you use these macros, don't modify bitset while iterating over it!
#define FOR_EACH_IN_BITSET_HELPER(v, bitset, i, sw, x) \
           for (int i=0;i<m;i++) {setword sw=bitset[i]; while (sw) {int x; TAKEBIT(x, sw); int v=i*WORDSIZE+x;
#define FOR_EACH_IN_BITSET(v, bitset) \
           FOR_EACH_IN_BITSET_HELPER(v, bitset, PASTE(i,__LINE__), PASTE(sw,__LINE__), PASTE(x,__LINE__))

#define END_FOR_EACH_IN_BITSET }}

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

int popcount(setword const *vv)
{
    int count = 0;
    for (int i=0; i<m; i++)
        count += POPCOUNT(vv[i]);
    return count;
}

struct Edge
{
    int v;
    int w;
    struct Edge *next;
};

void ll_insert(int *q_end, int *q_prev, int *q_next, int val, int list_idx, int n)
{
    int end = q_end[list_idx];
    q_end[list_idx] = val;
    q_prev[val] = end;
    q_next[val] = n + list_idx;
    q_next[end] = val;
}

void ll_delete(int *q_prev, int *q_next, int val)
{
    int prev = q_prev[val];
    int next = q_next[val];
    q_next[prev] = next;
    q_prev[next] = prev;
}

enum AdjSetType
{
    ASTypeList=0,
    ASTypeBitset=1,
    ASTypeNone=2
};

#define MAX_LIST_LEN 32

struct AdjSet
{
    enum AdjSetType type;
    int size;
    int list[MAX_LIST_LEN];
    setword *bitset;
    setword *fill_clique;
    struct AdjSet *adjset_containing_best_fill_clique;   // non-owning pointer
    int size_of_best_fill_clique;
    int fill_clique_ref_count;   // number of adjsets whose `adjset_containing_best_fill_clique` points here
};

void destroy_adjset(struct AdjSet *as)
{
    if (as->type == ASTypeBitset) {
        free_bitset(as->bitset);
    }
    if (as->fill_clique) {
        free_bitset(as->fill_clique);
    }
}

void add_to_adjset(struct AdjSet *as, int val)
{
    assert(as->type != ASTypeNone);
    if (as->type == ASTypeBitset) {
        ADDELEMENT(as->bitset, val);
    } else if (as->size == MAX_LIST_LEN) {
        as->type = ASTypeBitset;
        as->bitset = get_empty_bitset();
        for (int i=0; i<as->size; i++) {
            ADDELEMENT(as->bitset, as->list[i]);
        }
        ADDELEMENT(as->bitset, val);
    } else {
        as->list[as->size] = val;
    }
    ++as->size;
}

bool is_element_of_adjset(struct AdjSet *as, int val)
{
    assert(as->type != ASTypeNone);
    if (as->type == ASTypeBitset) {
        return ISELEMENT(as->bitset, val);
    } else {
        for (int i=0; i<as->size; i++) {
            if (as->list[i] == val) {
                return true;
            }
        }
        return false;
    }
}

bool are_adjacent(int u, int v, struct AdjSet *as)
{
    if (as[v].type == 0 && (as[u].type==1 || (as[v].size > as[u].size))) {
        return is_element_of_adjset(&as[u], v);
    }
    return is_element_of_adjset(&as[v], u);
}

void add_edge(int u, int w, int n, struct AdjSet *adjset,
        int *bucket_end, int *bucket_q_prev, int *bucket_q_next, int score_divisor)
{
    ll_delete(bucket_q_prev, bucket_q_next, u);
    ll_delete(bucket_q_prev, bucket_q_next, w);
    add_to_adjset(&adjset[u], w);
    add_to_adjset(&adjset[w], u);
    ll_insert(bucket_end, bucket_q_prev, bucket_q_next, u, adjset[u].size/score_divisor, n);
    ll_insert(bucket_end, bucket_q_prev, bucket_q_next, w, adjset[w].size/score_divisor, n);
}

void fill_using_bitset(setword *unmarked_nb_of_v_bitset, int n, struct AdjSet *adjset,
        int *bucket_end, int *bucket_q_prev, int *bucket_q_next, int score_divisor)
{
    FOR_EACH_IN_BITSET(u, unmarked_nb_of_v_bitset)
        // x is the unmarked neighbours of v that are not adjacent to u
        setword *x = get_copy_of_bitset(unmarked_nb_of_v_bitset);
        assert(adjset[u].type != ASTypeNone);
        if (adjset[u].type == ASTypeList) {
            for (int j=0; j<adjset[u].size; j++) {
                int w = adjset[u].list[j];
                DELELEMENT(x, w);
            }
        } else {
            for (int k=0; k<m; k++)
                x[k] &= ~adjset[u].bitset[k];
        }
        FOR_EACH_IN_BITSET(w, x)
            if (w >= u)
                break;
            add_edge(u, w, n, adjset, bucket_end, bucket_q_prev, bucket_q_next, score_divisor);
        END_FOR_EACH_IN_BITSET
        free_bitset(x);
    END_FOR_EACH_IN_BITSET
}

void fill_using_list(int *unmarked_nb_of_v, int unmarked_nb_of_v_len, int n, struct AdjSet *adjset,
        int *bucket_end, int *bucket_q_prev, int *bucket_q_next, int score_divisor)
{
    for (int j=0; j<unmarked_nb_of_v_len; j++) {
        int u = unmarked_nb_of_v[j];
        for (int k=j+1; k<unmarked_nb_of_v_len; k++) {
            int w = unmarked_nb_of_v[k];
            if (are_adjacent(u, w, adjset))
                continue;
            add_edge(u, w, n, adjset, bucket_end, bucket_q_prev, bucket_q_next, score_divisor);
        }
    }
}

void fill_vertex(int v, int n, struct AdjSet *adjset,
        int *bucket_end, int *bucket_q_prev, int *bucket_q_next,
        int *parent, int score_divisor, setword *marked, int *unmarked_nb_of_v)
{
    assert(adjset[v].type != ASTypeNone);
    if (adjset[v].type == ASTypeList) {
        int unmarked_nb_of_v_len = 0;
        for (int j=0; j<adjset[v].size; j++) {
            int u = adjset[v].list[j];
            if (!ISELEMENT(marked, u))
                unmarked_nb_of_v[unmarked_nb_of_v_len++] = u;
        }
        fill_using_list(unmarked_nb_of_v, unmarked_nb_of_v_len, n, adjset, bucket_end, bucket_q_prev, bucket_q_next, score_divisor);
    } else {
        setword *unmarked_nb_of_v_bitset = get_bitset();
        adjset[v].fill_clique = get_bitset();
        for (int k=0; k<m; k++) {
            unmarked_nb_of_v_bitset[k] = adjset[v].bitset[k] & ~marked[k];
            adjset[v].fill_clique[k] = unmarked_nb_of_v_bitset[k];
        }
        int pc = popcount(unmarked_nb_of_v_bitset);
        FOR_EACH_IN_BITSET(u, unmarked_nb_of_v_bitset)
            if (pc > adjset[u].size_of_best_fill_clique) {
                struct AdjSet *adjset_of_prev_best_fill_clique = adjset[u].adjset_containing_best_fill_clique;
                if (adjset_of_prev_best_fill_clique) {
                    --adjset_of_prev_best_fill_clique->fill_clique_ref_count;
                    if (adjset_of_prev_best_fill_clique->fill_clique_ref_count == 0) {
                        free_bitset(adjset_of_prev_best_fill_clique->fill_clique);
                        adjset_of_prev_best_fill_clique->fill_clique = NULL;
                    }
                }
                ++adjset[v].fill_clique_ref_count;
                adjset[u].adjset_containing_best_fill_clique = &adjset[v];
                adjset[u].size_of_best_fill_clique = pc;
            }
        END_FOR_EACH_IN_BITSET
        if (adjset[v].fill_clique_ref_count == 0) {
            // free up memory
            free_bitset(adjset[v].fill_clique);
            adjset[v].fill_clique = NULL;
        }

        bool can_avoid_fill = false;   // true if all vertices in unmarked_nb_of_v_bitset can be shown to be in a clique
        if (adjset[v].adjset_containing_best_fill_clique) {
//                    printf("%d   %d %d   %d\n", popcount(unmarked_nb_of_v_bitset),
//                            popcount(adjset[v].adjset_containing_best_fill_clique->fill_clique),
//                            adjset[v].size_of_best_fill_clique,
//                            popcount_of_set_difference(unmarked_nb_of_v_bitset, adjset[v].adjset_containing_best_fill_clique->fill_clique));
            setword *fill_clq = adjset[v].adjset_containing_best_fill_clique->fill_clique;
            can_avoid_fill = true;
            for (int k=0; k<m; k++) {
                if (unmarked_nb_of_v_bitset[k] & ~fill_clq[k]) {
                    can_avoid_fill = false;
                    break;
                }
            }
        }

        if (!can_avoid_fill) {
            if (popcount(unmarked_nb_of_v_bitset) > n / 64) {   // for speed, choose bitset version or not by a heuristic
                fill_using_bitset(unmarked_nb_of_v_bitset, n, adjset, bucket_end, bucket_q_prev, bucket_q_next, score_divisor);
            } else {
                int unmarked_nb_of_v_len = 0;
                FOR_EACH_IN_BITSET(u, unmarked_nb_of_v_bitset)
                    unmarked_nb_of_v[unmarked_nb_of_v_len++] = u;
                END_FOR_EACH_IN_BITSET
                fill_using_list(unmarked_nb_of_v, unmarked_nb_of_v_len, n, adjset, bucket_end, bucket_q_prev, bucket_q_next, score_divisor);
            }
        }
        free_bitset(unmarked_nb_of_v_bitset);
    }
    ADDELEMENT(marked, v);
//            printf("%d of %d\n", order_len, n);

    // find which vertices have v as parent
    assert(adjset[v].type != ASTypeNone);
    if (adjset[v].type == ASTypeList) {
        for (int j=0; j<adjset[v].size; j++) {
            int u = adjset[v].list[j];
            if (ISELEMENT(marked, u) && parent[u] == -1)
                parent[u] = v;
        }
    } else {
        FOR_EACH_IN_BITSET(u, adjset[v].bitset)
            if (ISELEMENT(marked, u) && parent[u] == -1)
                parent[u] = v;
        END_FOR_EACH_IN_BITSET
    }

    // free up some memory
    if (adjset[v].type == ASTypeBitset) {
        free_bitset(adjset[v].bitset);
        adjset[v].type = ASTypeNone;
    }
}

void naively_complete_tree_decomposition(int n, setword const *marked, int *parent)
{
    int v = -1;
    int i = 0;
    for (; i<n; i++) {
        if (!ISELEMENT(marked, i)) {
            for (int j=0; j<n; j++) {
                if (ISELEMENT(marked, j) && parent[j] == -1) {
                    parent[j] = i;
                }
            }
            v = i;
            i++;
            break;
        }
    }
    for (; i<n; i++) {
        if (!ISELEMENT(marked, i)) {
            parent[v] = i;
            v = i;
        }
    }
}

void fill_graph(int n, struct AdjSet *adjset, int *bucket_start,
        int *bucket_end, int *bucket_q_prev, int *bucket_q_next,
        int *parent, int score_divisor, int iternum)
{
    int fill_graph_time_limit = 30 * (iternum+1);
    clock_t start_t = clock();

    int *order = malloc(n * sizeof *order);
    int order_len = 0;

    setword *marked = get_empty_bitset();
    int *vv = malloc(n * sizeof *vv);
    int *unmarked_nb_of_v = malloc(n * sizeof *unmarked_nb_of_v);
    for (int i=0; i<n; i++) {
        print_decomp_and_exit_if_tle();
        int vv_len = 0;
        int v = bucket_start[i];
        while (v != n + i) {
//            printf("- %d\n", vv_len);
            vv[vv_len++] = v;
            v = bucket_q_next[v];
        }
        // vv is a list of vertices with adjacency list length i

        while (vv_len) {
            print_decomp_and_exit_if_tle();
            int v = -1;
            bool found_v = false;
            while (vv_len) {
                int rand_pos = KRAN(vv_len);
                v = vv[rand_pos];
                vv[rand_pos] = vv[vv_len-1];
                vv[vv_len-1] = v;
                --vv_len;
                if (!ISELEMENT(marked, v) && adjset[v].size/score_divisor == i) {
                    found_v = true;
                    break;
                }
            }
            if (!found_v)
                break;

            fill_vertex(v, n, adjset, bucket_end, bucket_q_prev, bucket_q_next,
                    parent, score_divisor, marked, unmarked_nb_of_v);
            order[order_len++] = v;
//            printf("%d of %d\n", order_len, n);
            if ((((double)(clock() - start_t))/CLOCKS_PER_SEC) > fill_graph_time_limit) {
                naively_complete_tree_decomposition(n, marked, parent);
                goto cleanup_fill_graph;
            }
        }
    }
cleanup_fill_graph:
    free_bitset(marked);
    free(vv);
    free(unmarked_nb_of_v);
    free(order);
}

//int tmp_c = 0;

idx_t *global_iperm;

int cmp_iperm(const void *a, const void *b)
{
    int v = *(const int *) a;
    int w = *(const int *) b;
    return global_iperm[v] - global_iperm[w];
}

void delete_incident_edges(int **nd, int *nd_len, int v)
{
    for (int i=0; i<nd_len[v]; i++) {
        int w = nd[v][i];
        for (int j=0; j<nd_len[w]; j++) {
            if (nd[w][j] == v) {
                nd[w][j] = nd[w][nd_len[w]-1];
                --nd_len[w];
                break;
            }
        }
    }
    nd_len[v] = 0;
}

bool try_to_add_k_vtx_chain(int **nd, int *nd_len, int *vv, int *parent, int start_pos, int end_pos, int *parent_v, int k,
        bool *vtx_unseen, int *tmp)
{
    if (end_pos - k <= start_pos) {
        return false;
    }

    for (int i=start_pos; i<end_pos - k; i++) {
        int v = vv[i];
        vtx_unseen[v] = true;
    }

    for (int i=end_pos - k; i<end_pos; i++) {
        // check that each of the final k vertices has a neighbour among
        // the other vertices
        int v = vv[i];
        bool found_neighbour = false;
        for (int j=0; j<nd_len[v]; j++) {
            int w = nd[v][j];
            if (vtx_unseen[w]) {
                found_neighbour = true;
                break;
            }
        }
        if (!found_neighbour) {
            for (int i=start_pos; i<end_pos - k; i++) {
                int v = vv[i];
                vtx_unseen[v] = false;
            }
            return false;
        }
    }

    int cursor = start_pos;
    int add_cursor = start_pos;
    int w = vv[start_pos];
    vtx_unseen[w] = false;
    tmp[add_cursor++] = w;
    while (cursor < add_cursor) {
        w = tmp[cursor++];
        for (int i=0; i<nd_len[w]; i++) {
            int u = nd[w][i];
            if (!vtx_unseen[u]) {
                continue;
            }
            vtx_unseen[u] = false;
            tmp[add_cursor++] = u;
        }
    }
    if (cursor == end_pos - k) {
        for (int i=0; i<k; i++) {
            int v = vv[end_pos - 1 - i];
            parent[v] = *parent_v;
            *parent_v = v;
            delete_incident_edges(nd, nd_len, v);
        }
        return true;
    } else {
        // re-zero memory
        for (int i=start_pos; i<end_pos - k; i++) {
            int v = vv[i];
            vtx_unseen[v] = false;
        }
        return false;
    }
}

struct Slice
{
    int start_pos;
    int end_pos;
};

int cmp_slice_len(const void *a, const void *b)
{
    struct Slice s0 = *(const struct Slice *) a;
    struct Slice s1 = *(const struct Slice *) b;
    int len0 = s0.end_pos - s0.start_pos;
    int len1 = s1.end_pos - s1.start_pos;
    if (len0 != len1)
        return len0 - len1;
    return s0.start_pos - s1.start_pos;
}

void add_parents_using_nd_order(int n, int **nd, int *nd_len, int *vv, int *parent, int start_pos, int end_pos, int parent_v,
        bool *vtx_unseen, int *reordered_vv, int *tmp)
{
    print_decomp_and_exit_if_tle();
    if (start_pos == end_pos) {
        return;
    }
//    qsort(vv + start_pos, end_pos-start_pos, sizeof *vv, cmp_iperm);

    print_decomp_and_exit_if_tle();
    for (int i=512; i>=1; i/=8) {
        while (try_to_add_k_vtx_chain(nd, nd_len, vv, parent, start_pos, end_pos, &parent_v, i, vtx_unseen, tmp)) {
            print_decomp_and_exit_if_tle();
            end_pos -= i;
//            tmp_c += i;
//            printf("tmp_c %d of %d\n", tmp_c, n);
        }
    }

    int subtree_root = vv[end_pos - 1];
    --end_pos;

    parent[subtree_root] = parent_v;
    int old_subtree_root_nd_len = nd_len[subtree_root];
    delete_incident_edges(nd, nd_len, subtree_root);
//    ++tmp_c;
//    printf("tmp_c %d of %d\n", tmp_c, n);

    if (start_pos == end_pos) {
        return;
    }
//    bool *vtx_unseen = calloc(n, sizeof *vtx_unseen);

    for (int i=start_pos; i<end_pos; i++) {
        int v = vv[i];
        vtx_unseen[v] = true;
    }

    struct Slice *component_slices = malloc(old_subtree_root_nd_len * sizeof *component_slices);

    int *vtx_to_component_num = tmp;

    int component_count = 0;
    int cursor = start_pos;
    int add_cursor = start_pos;
    int component_start = -1;
    for (int j=0; j<old_subtree_root_nd_len; j++) {
        // this is hacky, as nd[subtree_root] has kinda been deleted
        int w = nd[subtree_root][j];
        if (!vtx_unseen[w]) {
            continue;
        }
        vtx_unseen[w] = false;
        reordered_vv[add_cursor++] = w;
        vtx_to_component_num[w] = component_count;
        component_start = cursor;
        while (cursor < add_cursor) {
            w = reordered_vv[cursor++];
            for (int k=0; k<nd_len[w]; k++) {
                int u = nd[w][k];
                if (!vtx_unseen[u]) {
                    continue;
                }
                vtx_unseen[u] = false;
                reordered_vv[add_cursor++] = u;
                vtx_to_component_num[u] = component_count;
            }
        }
//        printf("? %d %d %d %d\n", component_start, cursor, end_pos, subtree_root);
        component_slices[component_count++] = (struct Slice) {component_start, cursor};
    }
    for (int i=0; i<component_count; i++) {
        // we'll re-add the vertices in sorted order in a moment
        component_slices[i].end_pos = component_slices[i].start_pos;
    }
    for (int i=start_pos; i<end_pos; i++) {
        int v = vv[i];
        int component_num = vtx_to_component_num[v];
        struct Slice *slice = &component_slices[component_num];
        reordered_vv[slice->end_pos++] = v;
    }
    qsort(component_slices, component_count, sizeof *component_slices, cmp_slice_len);
    for (int i=0; i<component_count-1; i++) {
        struct Slice slice = component_slices[i];
        add_parents_using_nd_order(n, nd, nd_len, reordered_vv, parent, slice.start_pos, slice.end_pos, subtree_root, vtx_unseen, vv, tmp);
    }
    int final_start_pos = component_slices[component_count-1].start_pos;
    int final_end_pos = component_slices[component_count-1].end_pos;
    free(component_slices);
    add_parents_using_nd_order(n, nd, nd_len, reordered_vv, parent, final_start_pos, final_end_pos, subtree_root, vtx_unseen, vv, tmp);
}

void make_elimination_tree_using_metis_nd(int n, int **nd, int *nd_len,
        int *parent, int iternum)
{
    idx_t *perm = malloc(n * sizeof *perm);
    idx_t *iperm = malloc(n * sizeof *iperm);
    global_iperm = iperm;

    params_t *params;

    params = (params_t *)malloc(sizeof(params_t));
    memset((void *)params, 0, sizeof(params_t));
    params->ctype         = METIS_CTYPE_SHEM;
    params->iptype        = (iternum / 6) % 2 ? METIS_IPTYPE_EDGE : METIS_IPTYPE_NODE;
    params->rtype         = METIS_RTYPE_SEP1SIDED;
  
    int ufactors[] = {30, 100, 1, 10, 200, 300};
    params->ufactor       = ufactors[iternum % 6];
    params->pfactor       = 0;
    params->compress      = 1;
    params->ccorder       = 0;
    params->no2hop        = 0;
  
    params->nooutput      = 0;
    params->wgtflag       = 1;
  
    params->nseps         = 3;
    if (iternum > 1)
        params->nseps     = 5;
    if (iternum > 5)
        params->nseps     = 8;
    if (iternum > 10)
        params->nseps     = 10;
    if (iternum > 25)
        params->nseps     = 15;
    params->niter         = 10;
  
    params->dbglvl        = 0;
  
    params->filename      = NULL;
    params->nparts        = 1;
    idx_t options[METIS_NOPTIONS];
    METIS_SetDefaultOptions(options);
    options[METIS_OPTION_CTYPE]    = params->ctype;
    options[METIS_OPTION_IPTYPE]   = params->iptype;
    options[METIS_OPTION_RTYPE]    = params->rtype;
    options[METIS_OPTION_DBGLVL]   = params->dbglvl;
    options[METIS_OPTION_UFACTOR]  = params->ufactor;
    options[METIS_OPTION_NO2HOP]   = params->no2hop;
    options[METIS_OPTION_COMPRESS] = params->compress;
    options[METIS_OPTION_CCORDER]  = params->ccorder;
    options[METIS_OPTION_NITER]    = params->niter;
    options[METIS_OPTION_NSEPS]    = params->nseps;
    options[METIS_OPTION_PFACTOR]  = params->pfactor;
    options[METIS_OPTION_NUMBERING]  = 0;


    int edge_count = 0;
    for (int i=0; i<n; i++)
        edge_count += nd_len[i];

    idx_t nvtxs = n;
    idx_t *xadj = malloc((n + 1) * sizeof *xadj);
    idx_t *adjncy = malloc(edge_count * 2 * sizeof *adjncy);
    int pos = 0;
    for (int i=0; i<n; i++) {
        xadj[i] = pos;
        for (int j=0; j<nd_len[i]; j++) {
            adjncy[pos++] = nd[i][j];
        }
    }
    xadj[n] = pos;

//    for (int i=0; i<n; i++) {
//        printf("%d\n", nd_len[i]);
//    }
//    exit(0);

    // copy nd and nd_len in order to delete incident edges as we go, for speed
    int *mutable_nd_len = malloc(n * sizeof *mutable_nd_len);
    int **mutable_nd = malloc(n * sizeof *mutable_nd);
    for (int i=0; i<n; i++) {
        mutable_nd[i] = malloc(nd_len[i] * sizeof(*mutable_nd[i]));
        mutable_nd_len[i] = nd_len[i];
        for (int j=0; j<nd_len[i]; j++) {
            mutable_nd[i][j] = nd[i][j];
        }
    }

    options[METIS_OPTION_SEED]     = metis_seed++;
    idx_t status = METIS_NodeND(&nvtxs, xadj, adjncy, NULL,
                 options, perm, iperm);

    bool *vtx_unseen = calloc(n, sizeof *vtx_unseen);
    int *reordered_vv = malloc(n * sizeof *reordered_vv);
    int *tmp = malloc(n * sizeof *tmp);
    int *vv = malloc(n * sizeof *vv);
    for (int i=0; i<n; i++) {
        vv[i] = perm[i];
    }
//    tmp_c = 0;

    add_parents_using_nd_order(n, mutable_nd, mutable_nd_len, perm, parent, 0, n, -1, vtx_unseen, reordered_vv, tmp);
//    printf("done\n");
    for (int i=0; i<n; i++) {
        free(mutable_nd[i]);
    }
    free(mutable_nd_len);
    free(mutable_nd);
    free(vtx_unseen);
    free(reordered_vv);
    free(tmp);
    free(vv);
    free(perm);
    free(iperm);
    free(params);
    free(xadj);
    free(adjncy);
}

int calculate_depths(int *vtx_depth, int const *parent, int n)
{
    for (int i=0; i<n; i++)
        vtx_depth[i] = 0;   // 0 means unknown
    int max_depth = 0;
    for (int i=0; i<n; i++) {
        print_decomp_and_exit_if_tle();
        int depth = 1;
        int v = i;
        while (parent[v] != -1) {
            v = parent[v];
            if (vtx_depth[v] != 0) {
                depth += vtx_depth[v];
                break;
            }
            ++depth;
        }
        vtx_depth[i] = depth;
        if (depth > max_depth)
            max_depth = depth;
    }
    return max_depth;
}

int heur_solve2(int **nd, int *nd_len, int n, int *parent, int *vtx_depth, int score_divisor, bool use_metis, int iternum)
{
    print_decomp_and_exit_if_tle();

    for (int i=0; i<n; i++) {
        parent[i] = -1;
    }

    if (use_metis) {
        make_elimination_tree_using_metis_nd(n, nd, nd_len, parent, iternum);
        return calculate_depths(vtx_depth, parent, n);
    }

    struct AdjSet *adjset = calloc(n, sizeof *adjset);
    for (int i=0; i<n; i++) {
        adjset[i].size_of_best_fill_clique = -1;
    }

    int *bucket_q_next = malloc(n * 2 * sizeof *bucket_q_next);
    int *bucket_q_prev = malloc(n * 2 * sizeof *bucket_q_prev);
    int *bucket_start = bucket_q_next + n;
    int *bucket_end = bucket_q_prev + n;
    for (int i=0; i<n; i++) {
        bucket_start[i] = n + i;
        bucket_end[i] = n + i;
    }

    for (int i=0; i<n; i++) {
        int len = nd_len[i];
        for (int j=0; j<len; j++) {
            add_to_adjset(&adjset[i], nd[i][j]);
        }
        ll_insert(bucket_end, bucket_q_prev, bucket_q_next, i, len/score_divisor, n);
    }

    fill_graph(n, adjset, bucket_start, bucket_end, bucket_q_prev, bucket_q_next, parent, score_divisor, iternum);

    int max_depth = calculate_depths(vtx_depth, parent, n);

    for (int i=0; i<n; i++)
        destroy_adjset(&adjset[i]);

    max_depth = 0;
    for (int i=0; i<n; i++) {
        if (vtx_depth[i] > max_depth)
            max_depth = vtx_depth[i];
    }

    deallocate_Bitsets();

    free(adjset);
    free(bucket_q_next);
    free(bucket_q_prev);

    return max_depth;
}

bool are_adj(int u, int v, int **nd, int *nd_len)
{
    for (int i=0; i<nd_len[u]; i++) {
        if (nd[u][i] == v) {
            return true;
        }
    }
    return false;
}

int get_vtx_ancestor_at_depth(int v, int d, int *parent, int *vtx_depth)
{
    if (vtx_depth[v] < d)
        return -1;
    int v_depth = vtx_depth[v];
    while (v_depth > d) {
        v = parent[v];
        --v_depth;
    }
    return v;
}

int improve_solution(int **nd, int *nd_len, int n, int *parent, int *vtx_depth, int score_divisor, int iter)
{
//    printf("improve %d\n", iter);
    int saved_m = m;

    int max_depth = 0;
    for (int i=0; i<n; i++) {
        if (vtx_depth[i] > max_depth)
            max_depth = vtx_depth[i];
    }

    // TODO: avoid using magic numbers in the loop below
    for (int subtree_height=max_depth-1; subtree_height>0; subtree_height--) {
//        printf("subtree_height %d\n", subtree_height);
        while (true) {
            if (subtree_height > max_depth)
                break;

            // singly-linked lists of children
            // TODO: maybe use doubly-linked lists and modify them when solution is improved
            int *child_list_start = malloc(n * sizeof *child_list_start);
            int *child_list_next = malloc(n * sizeof *child_list_next);
            for (int i=0; i<n; i++) {
                child_list_start[i] = -1;
            }
            for (int i=0; i<n; i++) {
                int p = parent[i];
//                printf("p %d\n", p);
                if (p != -1) {
                    child_list_next[i] = child_list_start[p];
                    child_list_start[p] = i;
                }
            }

            // find an ancestor of a vertex of max depth
            int v = 0;
            while (vtx_depth[v] != max_depth)
                ++v;

            for (int i=0; i<subtree_height - 1; i++)
                v = parent[v];

            int *q = malloc(n * sizeof *q);
            int q_start = 0;
            int q_len = 1;
            q[0] = v;
//            printf("!\n");
            while (q_start != q_len) {
//                printf("   %d\n", q_start);
                int v = q[q_start++];
                int child = child_list_start[v];
                while (child != -1) {
                    q[q_len++] = child;
                    child = child_list_next[child];
                }
            }
//            printf("q_len %d\n", q_len);

            int subgraph_n = q_len;
            int best_subtree_depth = INT_MAX;

            if (subgraph_n < iter * 50) {  // TODO: avoid magic number
                bool *old_vtx_used_in_subgraph = calloc(n, sizeof *old_vtx_used_in_subgraph);
                int *old_to_new_vtx = malloc(n * sizeof *old_to_new_vtx);

                for (int i=0; i<subgraph_n; i++) {
                    old_vtx_used_in_subgraph[q[i]] = true;
                    old_to_new_vtx[q[i]] = i;
                }

                int **subgraph_nd = malloc(subgraph_n * sizeof *subgraph_nd);
                int *subgraph_nd_len = calloc(subgraph_n, sizeof *subgraph_nd_len);
                for (int i=0; i<subgraph_n; i++) {
                    // First, calculate how much memory is needed...
                    int old_v = q[i];
                    for (int j=0; j<nd_len[old_v]; j++) {
                        int old_w = nd[old_v][j];
                        subgraph_nd_len[i] += old_vtx_used_in_subgraph[old_w];
                    }
                    // ... then create the adjacency list
                    subgraph_nd[i] = malloc(subgraph_nd_len[i] * sizeof *subgraph_nd[i]);
                    subgraph_nd_len[i] = 0;
                    for (int j=0; j<nd_len[old_v]; j++) {
                        int old_w = nd[old_v][j];
                        if (old_vtx_used_in_subgraph[old_w]) {
                            subgraph_nd[i][subgraph_nd_len[i]++] = old_to_new_vtx[old_w];
                        }
                    }
                }
                
                m = SETWORDSNEEDED(subgraph_n);
                int *new_parent = malloc(subgraph_n * sizeof *new_parent);
                int *new_vtx_depth = malloc(subgraph_n * sizeof *new_vtx_depth);
                for (int i=0; i<(iter<10 ? 2 : 10); i++) {   // TODO: avoid magic numbers
                    int subtree_depth = heur_solve2(subgraph_nd, subgraph_nd_len, subgraph_n, new_parent, new_vtx_depth, score_divisor, subgraph_n > 150 && i%2, i);
                    if (subtree_depth < subtree_height) {
//                        printf("subtree depth %d\n", subtree_depth);
                        best_subtree_depth = subtree_depth;

                        int subtree_root = v;
                        int parent_of_subtree_root = parent[subtree_root];
                        int subtree_root_depth = vtx_depth[v];
                        for (int i=0; i<subgraph_n; i++) {
                            if (new_parent[i] == -1) {
                                parent[q[i]] = parent_of_subtree_root;
                            } else {
                                parent[q[i]] = q[new_parent[i]];
                            }
                            vtx_depth[q[i]] = subtree_root_depth - 1 + new_vtx_depth[i];
                        }

                        break;
                    }
                }
                free(new_parent);
                free(new_vtx_depth);

                for (int i=0; i<subgraph_n; i++)
                    free(subgraph_nd[i]);
                free(subgraph_nd);
                free(subgraph_nd_len);
                free(old_vtx_used_in_subgraph);
                free(old_to_new_vtx);
            }
            free(child_list_start);
            free(child_list_next);
            free(q);

            if (best_subtree_depth >= subtree_height)
                break;

            max_depth = 0;
            for (int i=0; i<n; i++) {
                if (vtx_depth[i] > max_depth)
                    max_depth = vtx_depth[i];
            }
        }
    }

    m = saved_m;
    return max_depth;
}

void update_incumbent_if_necessary(int n, int new_d, int *parent, int *vtx_depth, int *best, int *saved_parent, int *saved_vtx_depth)
{
    if (new_d < *best) {
//        printf("* %d\n", new_d);
        for (int i=0; i<n; i++) {
            saved_parent[i] = parent[i];
            saved_vtx_depth[i] = vtx_depth[i];
        }
        *best = new_d;
    }
}

int main(int argc, char *argv[])
{
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_handler = term;
    sigaction(SIGTERM, &action, NULL);

    char s[BUFFERSIZE], s1[32], s2[32];
    int n, edge_count;
    struct Edge edge_list_head = {0};
    struct Edge *edge_list_tail = &edge_list_head;
    int v, w;
    int num_edges_read = 0;
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
            global_n = n;
            m = SETWORDSNEEDED(n);
            break;
        default:
            if (sscanf(s, "%d %d", &v, &w) != 2)
                exit(1);
            if (v == w)
                continue;
            --v;
            --w;
            struct Edge *edge = malloc(sizeof *edge);
            edge_list_tail->next = edge;
            edge->v = v;
            edge->w = w;
            edge->next = NULL;
            edge_list_tail = edge;
            ++num_edges_read;
        }
    }

    struct Edge *e = edge_list_head.next;
    while (e) {
//        printf("edge %d %d\n", e->v, e->w);
        e = e->next;
    }

    nd_len = calloc(n, sizeof *nd_len);
    e = edge_list_head.next;
    while (e) {
        ++nd_len[e->v];
        ++nd_len[e->w];
        e = e->next;
    }
    nd = malloc(n * sizeof *nd);
    for (int i=0; i<n; i++) {
        nd[i] = malloc(nd_len[i] * sizeof(*nd[i]));
        nd_len[i] = 0;
    }
    e = edge_list_head.next;
    while (e) {
        nd[e->v][nd_len[e->v]++] = e->w;
        nd[e->w][nd_len[e->w]++] = e->v;
        e = e->next;
    }

    e = edge_list_head.next;
    while (e) {
        struct Edge *next_e = e->next;
        free(e);
        e = next_e;
    }

    saved_parent = calloc(n, sizeof *saved_parent);
    int *saved_depth = calloc(n, sizeof *saved_depth);
    int *parent = malloc(n * sizeof *parent);
    int *vtx_depth = malloc(n * sizeof *vtx_depth);
    best = n;
    for (int i=0; i<n; i++) {
        saved_parent[i] = i - 1;
    }

    clock_t start_t = clock();

    // we have five phases: non-Metis without improvements, Metis without improvements, Metis with improvements, non-Metis without and with improvements
    int phase = 0;
    bool use_metis = false;
    bool make_improvements = false;

    int MINUTE_LEN = 60;

    for (int i=0; i<INT_MAX; i++) {
        if (phase == 0 && (((double)(clock() - start_t))/CLOCKS_PER_SEC) > 3 * MINUTE_LEN) {
            phase = 1;
            use_metis = true;
            make_improvements = false;
            i = 0;
        } else if (phase == 1 && (((double)(clock() - start_t))/CLOCKS_PER_SEC) > 11 * MINUTE_LEN) {
            phase = 2;
            use_metis = true;
            make_improvements = true;
            i = 0;
        } else if (phase == 2 && (((double)(clock() - start_t))/CLOCKS_PER_SEC) > 20 * MINUTE_LEN) {
            phase = 3;
            use_metis = false;
            make_improvements = false;
            i = 0;
        } else if (phase == 3 && (((double)(clock() - start_t))/CLOCKS_PER_SEC) > 23 * MINUTE_LEN) {
            phase = 4;
            use_metis = false;
            make_improvements = true;
            i = 0;
        }
//        printf("phase %d   i %d\n", phase, i);
        int new_d = heur_solve2(nd, nd_len, n, parent, vtx_depth, use_metis || (i%2==0) ? 1 : i/2 % 3 + 1, use_metis, i);
//        printf("   i' %d\n", i);
//        for (int j=0; j<10; j++) {
//            new_d = improve_solution(nd, nd_len, n, parent, vtx_depth);
//        }
//        printf("** %d\n", new_d);
        update_incumbent_if_necessary(n, new_d, parent, vtx_depth, &best, saved_parent, saved_depth);
        if (make_improvements && n < 300000 && i > 30) {
            int top_k = i/100 + 1;
            bool increased_top_k = false;
            bool time_almost_up = (((double)(clock() - start_t))/CLOCKS_PER_SEC) > 28 * MINUTE_LEN;
            if (time_almost_up) {
                top_k = INT_MAX;
                increased_top_k = true;
                // restore best solution so far and try to improve it
                for (int i=0; i<n; i++) {
                    parent[i] = saved_parent[i];
                    vtx_depth[i] = saved_depth[i];
                }
                new_d = best;
            }
            for (int k=0; k<top_k; k++) {
                print_decomp_and_exit_if_tle();
                for (int j=0; j<i/100 + 3; j++) {
                    new_d = improve_solution(nd, nd_len, n, parent, vtx_depth, j%2 ? 1 : ((j/2)%3 + 1), i - 30);
                }
                if (new_d <= best && !increased_top_k) {
                    top_k *= 3;
                    increased_top_k = true;
                }
                update_incumbent_if_necessary(n, new_d, parent, vtx_depth, &best, saved_parent, saved_depth);
            }
        }
        print_decomp_and_exit_if_tle();
    }
    printf("%d\n", best);
    for (int i=0; i<n; i++) {
        printf("%d\n", saved_parent[i] + 1);
    }
    free(saved_parent);
    free(parent);
    free(vtx_depth);
}
