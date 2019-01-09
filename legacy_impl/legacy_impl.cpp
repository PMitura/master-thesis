#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <queue>
#include <cstring>
#include <algorithm>
using namespace std;

int n, m, k;
int ** dst, ** path_next, ** dp;
int * parent, * dist, * closed;
int ** dp_par;
vector<int> terms;
vector<vector<pair<int, int>>> graph;
bool * is_term;
map<int, int> terms_to_ids;
map<int, int> orig_to_prep, prep_to_orig;
vector<pair<int, int>> preselected_edges;
int preselected_value;
set<pair<int, int>> banned_edges;

map<pair<int, int>, vector<pair<int, int>>> compressed_paths;

const int INFTY = 1 << 29;

void floyd_warshall() {
    for (int t = 0; t < n; t++) {
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (dst[i][j] > dst[i][t] + dst[t][j]) {
                    dst[i][j] = dst[i][t] + dst[t][j];
                    path_next[i][j] = path_next[i][t];
                }
            }
        }
    }
}

void read_input_matrix() {
    // read vertex and edge count
    string s; cin >> s >> s >> s;
    cin >> n >> s >> m;

    // setup n^2 vertex distance and shortest path successor matrices
    dst = new int*[n];
    path_next = new int*[n];
    for (int i = 0; i < n; i++) {
        dst[i] = new int[n];
        path_next[i] = new int[n];
        for (int j = 0; j < n; j++) {
            dst[i][j] = INFTY;
        }
        dst[i][i] = 0;
    }

    // read weighted edge list
    for (int i = 0; i < m; i++) {
        cin >> s;
        int x, y, w; cin >> x >> y >> w;
        x--; y--;
        dst[x][y] = w;
        dst[y][x] = w;
        path_next[x][y] = y;
        path_next[y][x] = x;
    }

    // read terminal list
    cin >> s >> s >> s >> s;
    cin >> k;
    is_term = new bool[n];
    for (int i = 0; i < n; i++) {
        is_term[i] = 0;
    }
    if (k >= 32) exit(1);
    for (int i = 0; i < k; i++) {
        cin >> s;
        int x; cin >> x; x--;
        is_term[x] = 1;
        terms.push_back(x);
        terms_to_ids[i] = x;
    }
}

void read_input_nlist() {
    // read vertex and edge count
    string s; cin >> s >> s >> s;
    cin >> n >> s >> m;

    // setup adjacency list representation
    graph.resize(n);

    // read weighted edge list
    for (int i = 0; i < m; i++) {
        cin >> s;
        int x, y, w; cin >> x >> y >> w;
        x--; y--;
        graph[x].push_back({y, w});
        graph[y].push_back({x, w});
    }

    // read terminal list
    cin >> s >> s >> s >> s;
    cin >> k;
    is_term = new bool[n];
    for (int i = 0; i < n; i++) {
        is_term[i] = 0;
    }
    // if (k >= 32) exit(1);
    for (int i = 0; i < k; i++) {
        cin >> s;
        int x; cin >> x; x--;
        is_term[x] = 1;
        terms.push_back(x);
        terms_to_ids[i] = x;
    }
}

pair<int, int> ** dp_par_dw;
void dw_backtrack(unsigned subs, int vtx, vector<pair<int, int>>& tree) {
    if (__builtin_popcount(subs) == 1) {
        int from = vtx, to = terms_to_ids[__builtin_ffs(subs)-1];
        while (from != to) {
            tree.push_back({from, path_next[from][to]});
            from = path_next[from][to];
        }
        return;
    }

    if (dp_par_dw[subs][vtx].second) {
        dw_backtrack(dp_par_dw[subs][vtx].first, vtx, tree);
        dw_backtrack(subs - dp_par_dw[subs][vtx].first, vtx, tree);
        return;
    }

    int from = vtx, to = dp_par_dw[subs][vtx].first;
    while (from != to) {
        tree.push_back({from, path_next[from][to]});
        from = path_next[from][to];
    }
    dw_backtrack(subs, dp_par_dw[subs][vtx].first, tree);
}

void print_result_dw() {
    int full = (1 << k) - 1;
    cout << "VALUE " << dp[full][terms[0]] << endl;

    vector<pair<int, int>> tree;
    dw_backtrack(full, terms[0], tree);
    for (auto i : tree) {
        cout << (i.first)+1 << " " << (i.second)+1 << endl;
    }
}

void dreyfus_wagner() {
    read_input_matrix();
    floyd_warshall();

    // intialize dynamic programming caches
    dp = new int*[1 << k];
    dp_par_dw = new pair<int, int>*[1 << k];
    for (int i = 0; i < (1 << k); i++) {
        dp[i] = new int[n];
        for (int j = 0; j < n; j++) {
            dp[i][j] = INFTY;
        }
        dp_par_dw[i] = new pair<int, int>[n];
    }

    // initial values of subsets only containing one terminal
    int enumerate = 0;
    for (auto i : terms) {
        dp[1 << enumerate][i] = 0;
        enumerate++;
    }


    // for all subsets of terminals
    for (int subset = 1; subset < (1 << k); subset++) {
        for (int d = (subset - 1) & subset; d != 0; d = (d - 1) & subset) {
            for (int root = 0; root < n; root++) {
                if (dp[subset][root] > dp[d][root] + dp[subset - d][root]) {
                    dp[subset][root] = dp[d][root] + dp[subset - d][root];
                    dp_par_dw[subset][root] = {d, 1};
                }
            }
        }

        for (int fork = 0; fork < n; fork++) {
            for (int root = 0; root < n; root++) {
                if (dp[subset][root] > dp[subset][fork] + dst[root][fork]) {
                    dp[subset][root] = dp[subset][fork] + dst[root][fork];
                    dp_par_dw[subset][root] = {fork, 0};
                }
            }
        }
    }

    print_result_dw();
}

void backtrack_emv(int subset, int root, vector<pair<int, int>>& tree) {
    if (__builtin_popcount(subset) == 1) {
        memset(closed, 0, sizeof(int)*n);
        priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> dijkstra_q;
        for (int i = 0; i < n; i++) {
            dist[i] = INFTY;
            parent[i] = -1;
        }

        int from = terms[__builtin_ffs(subset)-1];
        dist[from] = 0;
        dijkstra_q.push({dist[from], from});
        while (dijkstra_q.size()) {
            pair<int, int> curr = dijkstra_q.top();
            dijkstra_q.pop();
            if (closed[curr.second]) continue;
            closed[curr.second] = 1;
            for (auto adj : graph[curr.second]) {
                if (closed[adj.first]) continue;
                if (dist[adj.first] > curr.first + adj.second) {
                    dist[adj.first] = curr.first + adj.second;
                    parent[adj.first] = curr.second;
                    dijkstra_q.push({dist[adj.first], adj.first});
                }
            }
        }

        int curr = root, prev = parent[curr];
        while (prev != -1) {
            tree.push_back({curr, prev});
            curr = prev;
            prev = parent[curr];
        }
        return;
    }

    memset(closed, 0, sizeof(int)*n);
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> dijkstra_q;
    for (int i = 0; i < n; i++) {
        dist[i] = dp[dp_par[subset][i]][i] 
                + dp[subset - dp_par[subset][i]][i];
        parent[i] = -1;
        dijkstra_q.push({dist[i], i});
    }
    while (dijkstra_q.size()) {
        pair<int, int> curr = dijkstra_q.top();
        dijkstra_q.pop();
        if (closed[curr.second]) continue;
        closed[curr.second] = 1;
        for (auto adj : graph[curr.second]) {
            if (closed[adj.first]) continue;
            if (dist[adj.first] > curr.first + adj.second) {
                dist[adj.first] = curr.first + adj.second;
                parent[adj.first] = curr.second;
                dijkstra_q.push({dist[adj.first], adj.first});
            }
        }
    }

    int curr = root, prev = parent[curr];
    while (prev != -1) {
        tree.push_back({curr, prev});
        curr = prev;
        prev = parent[curr];
    }

    backtrack_emv(dp_par[subset][curr], curr, tree);
    backtrack_emv(subset - dp_par[subset][curr], curr, tree);
}

void print_result_emv() {
    cout << "VALUE " << dp[(1 << k) - 1][terms[0]] + preselected_value << endl;
    vector<pair<int, int>> edges;
    backtrack_emv((1 << k) - 1, terms[0], edges);
    for (auto i : edges) {
        pair<int, int> edge_pair = minmax(prep_to_orig[i.first], prep_to_orig[i.second]);
        if (compressed_paths.count(edge_pair)) {
            for (auto comp_edge : compressed_paths[edge_pair]) {
                cout << comp_edge.first + 1 << " " << comp_edge.second + 1 << endl;
            }
        } else {
            cout << prep_to_orig[i.first] + 1 << " " << prep_to_orig[i.second] + 1 << endl;
        }
    }
    for (auto i : preselected_edges) {
        cout << i.first + 1 << " " << i.second + 1 << endl;
    }
}

void preprocess() {
    // convert adjacency list to adjacency set
    vector<map<int, int>> adj_sets(n);
    for (int i = 0; i < n; i++) {
        for (auto nb : graph[i]) {
            adj_sets[i][nb.first] = nb.second;
        }
    }

    // find all leaves in the initial graph
    vector<int> leaves;
    for (int i = 0; i < n; i++) {
        if (adj_sets[i].size() == 1) {
            leaves.push_back(i);
        }
    }

    // prune all leaves (including the newly created ones)
    bool * deleted = new bool[n];
    memset(deleted, 0, sizeof(bool)*n);
    while (!leaves.empty()) {
        int cur = leaves.back();
        // cout << "  Processing leaf: " << cur << endl;
        leaves.pop_back();
        int nb = (*(adj_sets[cur].begin())).first;
        deleted[cur] = 1;
        if (is_term[cur]) {
            preselected_edges.push_back({cur, nb});
            preselected_value += (*(adj_sets[cur].begin())).second;
            is_term[nb] = 1;
        }
        adj_sets[nb].erase(cur);
        if (adj_sets[nb].size() == 1) {
            leaves.push_back(nb);
        }
    }

    // remove all non-terminals with degree 2 (path compression)
    for (int i = 0; i < n; i++) {
        if (!deleted[i] && !is_term[i] && adj_sets[i].size() == 2) {
            int ctr = 0, nbs[2], weight = 0;
            for (auto i_nb : adj_sets[i]) {
                adj_sets[i_nb.first].erase(i);
                nbs[ctr++] = i_nb.first;
                weight += i_nb.second;
            }
            if (!adj_sets[nbs[0]].count(nbs[1]) ||
                adj_sets[nbs[0]][nbs[1]] > weight) {
                adj_sets[nbs[0]][nbs[1]] = weight;
                adj_sets[nbs[1]][nbs[0]] = weight;

                pair<int, int> comp_edge = minmax(nbs[0], nbs[1]);
                if (compressed_paths.count(minmax(nbs[0], i))) {
                    for (auto precomp : compressed_paths[minmax(nbs[0], i)]) {
                        compressed_paths[comp_edge].push_back(precomp);
                    }
                } else {
                    compressed_paths[comp_edge].push_back({nbs[0], i});
                }
                if (compressed_paths.count(minmax(nbs[1], i))) {
                    for (auto precomp : compressed_paths[minmax(nbs[1], i)]) {
                        compressed_paths[comp_edge].push_back(precomp);
                    }
                } else {
                    compressed_paths[comp_edge].push_back({nbs[1], i});
                }

            }
            deleted[i] = 1;
        }
    }

    // remap back to adjacency list
    int counter = 0;
    int new_k = 0;
    terms.clear();
    bool * new_terms = new bool[n];
    memset(new_terms, 0, sizeof(bool) * n);
    for (int i = 0; i < n; i++) {
        if (!deleted[i]) {
            orig_to_prep[i] = counter;
            prep_to_orig[counter] = i;
            if (is_term[i]) {
                new_k++;
                new_terms[counter] = 1;
                terms.push_back(counter);
            }
            counter++;
        }
    }

    int new_n = counter;
    for (int i = 0; i < new_n; i++) {
        graph[i].clear();
        for (auto j : adj_sets[prep_to_orig[i]]) {
            graph[i].push_back({orig_to_prep[j.first], j.second});
        }
    }
    for (int i = new_n; i < n; i++) {
        graph[i].clear();
    }
    n = new_n;
    k = new_k;
    delete[] is_term;
    delete[] deleted;
    is_term = new_terms;
}

void erickson_monma_veinott() {
    read_input_nlist();
    // cout << "Before preprocess n: " << n << " k: " << k << endl;
    preprocess();
    // cout << "After preprocess n: " << n << " k: " << k << endl;

    // intialize dynamic programming caches
    dp = new int*[1 << k];
    dp_par = new int*[1 << k];
    for (int i = 0; i < (1 << k); i++) {
        dp[i] = new int[n];
        for (int j = 0; j < n; j++) {
            dp[i][j] = i ? INFTY : 0;
        }
        dp_par[i] = new int[n];
    }
    closed = new int[n];
    dist   = new int[n];
    parent = new int[n];

    // initial values of subsets only containing one terminal
    int enumerate = 0;
    for (auto i : terms) {
        dp[1 << enumerate][i] = 0;
        enumerate++;
    }

    // for all subsets of terminals
    for (int subset = 1; subset < (1 << k); subset++) {
        int most_sig = (1 << 31) >> __builtin_clz(subset);
        for (int d = (subset - 1) & subset; d & most_sig; d = (d - 1) & subset) {
            for (int root = 0; root < n; root++) {
                if (dp[subset][root] > dp[d][root] + dp[subset - d][root]) {
                    dp[subset][root] = dp[d][root] + dp[subset - d][root];
                    dp_par[subset][root] = d;
                }
            }
        }

        memset(closed, 0, sizeof(int)*n);
        priority_queue<pair<int, int>, vector<pair<int, int>>, 
            greater<pair<int, int>>> dijkstra_q;
        for (int i = 0; i < n; i++) {
            dijkstra_q.push({dp[subset][i], i});
            dist[i] = dp[subset][i];
        }
        while (dijkstra_q.size()) {
            pair<int, int> curr = dijkstra_q.top();
            dijkstra_q.pop();
            if (closed[curr.second]) continue;
            closed[curr.second] = 1;
            for (auto adj : graph[curr.second]) {
                if (closed[adj.first]) continue;
                if (dist[adj.first] > curr.first + adj.second) {
                    dist[adj.first] = curr.first + adj.second;
                    dijkstra_q.push({dist[adj.first], adj.first});
                }
            }
        }

        for (int i = 0; i < n; i++) {
            dp[subset][i] = dist[i];
        }
    }

    print_result_emv();
}

// only returns, whether there is a steiner tree of given weight
int nederlof_instance(int weight) {
    int ** neder_dp = new int*[n];
    for (int i = 0; i < n; i++) {
        neder_dp[i] = new int[weight];
    }
    map<int, int> term_map;
    int counter = 0;
    for (auto i : terms) {
        term_map[i] = counter++;
    }

    unsigned ** bw_counter = new unsigned*[n];
    for (int i = 0; i < n; i++) {
        bw_counter[i] = new unsigned[weight];
        memset(bw_counter[i], 0, sizeof(unsigned) * weight);
    }

    for (int subset = 0; subset < (1 << k); subset++) {
        // uncomment to enable progress reports
        // cout << "Done: " << (double) subset / (1 << k) << endl;
        for (int i = 0; i < n; i++) {
            memset(neder_dp[i], 0, sizeof(int) * weight);
            neder_dp[i][0] = 1;
        }
        for (int w = 1; w < weight; w++) {
            for (int x = 0; x < n; x++) {
                // instance for b(x, w)
                for (auto i : graph[x]) {
                    pair<int, int> edge = minmax(x, i.first);
                    if (banned_edges.count(edge)) continue;
                    if (       is_term[i.first]
                            && (subset & (1 << term_map[i.first]))) {
                            continue;
                    }
                    for (int dif = 0; dif <= w - i.second; dif++) {
                        // "modular arithmetics", for now with base = 2^32-1
                        // TODO: rerun with a different module
                        neder_dp[x][w] += neder_dp[i.first][dif]
                            * neder_dp[x][w - i.second - dif];
                    }
                }
            }
            // compute intermediate result of in/ex
            int sign = (__builtin_popcount(subset) & 1) ? -1 : 1;
            for (int i = 0; i < n; i++) {
                bw_counter[i][w] += neder_dp[i][w] * sign;
            }
        }
    }

    int result = -1;
    for (int w = 0; w < weight; w++) {
        for (int i = 0; i < n; i++) {
            if (bw_counter[i][w]) {
                result = w;
                break;
            }
        }
        if (result != -1) break;
    }

    for (int i = 0; i < n; i++) {
        delete[] neder_dp[i];
        delete[] bw_counter[i];
    }
    delete[] neder_dp;
    delete[] bw_counter;

    return result;
}

void nederlof() {
    read_input_nlist();
    int max_weight = 1000;
    int tree_weight = nederlof_instance(max_weight);

    vector<pair<int, int>> used_edges;
    for (int node = 0; node < n; node++) {
        for (auto adj : graph[node]) {
            if (node > adj.first) continue;
            banned_edges.insert({node, adj.first});
            int reduced_tree_weight = nederlof_instance(max_weight);
            if (reduced_tree_weight != tree_weight) {
                used_edges.push_back({node, adj.first});
                banned_edges.erase({node, adj.first});
            }
        }
    }

    cout << "VALUE " << tree_weight << endl;
    for (auto edge : used_edges) {
        cout << edge.first + 1 << " " << edge.second + 1 << endl;
    }
}

int main() {
    ios::sync_with_stdio(0);

    // dreyfus_wagner();
    erickson_monma_veinott();
    // nederlof();

    return 0;
}
