#include <iostream>
#include <vector>
#include <numeric>
#include <algorithm>
#include <queue>
#include <cstdlib>

using namespace std;

int get_girth(int n, const vector<int>& adj) {
    int g = 1000000;
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            if (adj[i] & (1 << j)) {
                vector<int> dist(n, -1);
                queue<int> q;
                q.push(i);
                dist[i] = 0;
                while (!q.empty()) {
                    int u = q.front(); q.pop();
                    if (dist[u] >= g) break;
                    for (int v = 0; v < n; ++v) {
                        if (u == i && v == j) continue;
                        if (u == j && v == i) continue;
                        if (adj[u] & (1 << v)) {
                            if (dist[v] == -1) {
                                dist[v] = dist[u] + 1;
                                q.push(v);
                                if (v == j) break;
                            }
                        }
                    }
                }
                if (dist[j] != -1) {
                    g = min(g, dist[j] + 1);
                }
            }
        }
    }
    return g == 1000000 ? 0 : g;
}

int max_induced_tree(int n, const vector<int>& adj) {
    int max_t = 0;
    for (int mask = 1; mask < (1 << n); ++mask) {
        int sz = __builtin_popcount(mask);
        if (sz <= max_t) continue;
        int edges = 0;
        for (int i = 0; i < n; ++i) {
            if (mask & (1 << i)) {
                edges += __builtin_popcount(adj[i] & mask);
            }
        }
        edges /= 2;
        if (edges != sz - 1) continue;
        int start = __builtin_ctz(mask);
        int visited = 0;
        queue<int> q;
        q.push(start);
        visited |= (1 << start);
        while (!q.empty()) {
            int u = q.front(); q.pop();
            int nbs = adj[u] & mask & ~visited;
            while (nbs) {
                int v = __builtin_ctz(nbs);
                visited |= (1 << v);
                q.push(v);
                nbs &= ~(1 << v);
            }
        }
        if (visited == mask) {
            max_t = sz;
        }
    }
    return max_t;
}

int get_ecc_centers(int n, const vector<int>& adj) {
    vector<vector<int>> dist(n, vector<int>(n, 1000000));
    for (int i = 0; i < n; ++i) {
        dist[i][i] = 0;
        queue<int> q;
        q.push(i);
        while (!q.empty()) {
            int u = q.front(); q.pop();
            for (int v = 0; v < n; ++v) {
                if (adj[u] & (1 << v)) {
                    if (dist[i][v] > dist[i][u] + 1) {
                        dist[i][v] = dist[i][u] + 1;
                        q.push(v);
                    }
                }
            }
        }
    }
    vector<int> ecc(n, 0);
    int min_ecc = 1000000;
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            ecc[i] = max(ecc[i], dist[i][j]);
        }
        min_ecc = min(min_ecc, ecc[i]);
    }
    vector<int> centers;
    for (int i = 0; i < n; ++i) {
        if (ecc[i] == min_ecc) centers.push_back(i);
    }
    int max_d = 0;
    for (int i = 0; i < n; ++i) {
        int min_to_c = 1000000;
        for (int c : centers) {
            min_to_c = min(min_to_c, dist[i][c]);
        }
        max_d = max(max_d, min_to_c);
    }
    return max_d;
}

int main() {
    int n = 10;
    cout << "Random search for n=10" << endl;
    srand(42);
    long long max_edges = n * (n - 1) / 2;
    for (long long iter = 0; iter < 500000; ++iter) {
        vector<int> adj(n, 0);
        int e = 0;
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                if (rand() % 2) {
                    adj[i] |= (1 << j);
                    adj[j] |= (1 << i);
                }
                e++;
            }
        }
        // Check connectivity
        int visited = 1;
        queue<int> q;
        q.push(0);
        while (!q.empty()) {
            int u = q.front(); q.pop();
            int nbs = adj[u] & ~visited;
            while (nbs) {
                int v = __builtin_ctz(nbs);
                visited |= (1 << v);
                q.push(v);
                nbs &= ~(1 << v);
            }
        }
        if (visited != (1 << n) - 1) continue;
        
        int t = max_induced_tree(n, adj);
        int g = get_girth(n, adj);
        int ecc = get_ecc_centers(n, adj);
        if (t < g - 1 + ecc) {
            cout << "Counterexample found! n=" << n << endl;
            cout << "tree=" << t << " girth=" << g << " ecc=" << ecc << endl;
            for(int i=0; i<n; ++i) cout << adj[i] << " ";
            cout << endl;
            return 0;
        }
    }
    cout << "No counterexamples in 500k random graphs." << endl;
    return 0;
}
