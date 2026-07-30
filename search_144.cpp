#include <iostream>
#include <vector>
#include <string>
#include <queue>
#include <algorithm>

using namespace std;

// Decode graph6 to adjacency matrix
vector<vector<int>> decode_graph6(const string& g6) {
    int n = g6[0] - 63;
    if (n < 0 || n > 62) { /* simplified */ }
    vector<vector<int>> adj(n, vector<int>(n, 0));
    int k = 1;
    int bit_count = 0;
    int current_val = g6[k] - 63;
    
    for (int i = 1; i < n; ++i) {
        for (int j = 0; j < i; ++j) {
            int bit = (current_val >> (5 - bit_count)) & 1;
            if (bit) {
                adj[i][j] = 1;
                adj[j][i] = 1;
            }
            bit_count++;
            if (bit_count == 6) {
                bit_count = 0;
                k++;
                if (k < g6.length())
                    current_val = g6[k] - 63;
            }
        }
    }
    return adj;
}

int main() {
    string line;
    while (getline(cin, line)) {
        if (line.empty()) continue;
        int n = line[0] - 63;
        auto adj = decode_graph6(line);
        
        // 1. Check connectedness and eccentricities
        vector<vector<int>> dist(n, vector<int>(n, 1e9));
        for(int i=0; i<n; ++i) {
            dist[i][i] = 0;
            queue<int> q; q.push(i);
            while(!q.empty()) {
                int u = q.front(); q.pop();
                for(int v=0; v<n; ++v) {
                    if(adj[u][v] && dist[i][v] > dist[i][u] + 1) {
                        dist[i][v] = dist[i][u] + 1;
                        q.push(v);
                    }
                }
            }
        }
        
        bool connected = true;
        vector<int> ecc(n, 0);
        int rad = 1e9;
        for(int i=0; i<n; ++i) {
            for(int j=0; j<n; ++j) {
                if(dist[i][j] > 1e8) connected = false;
                ecc[i] = max(ecc[i], dist[i][j]);
            }
            rad = min(rad, ecc[i]);
        }
        if(!connected) continue;
        
        vector<int> centers;
        for(int i=0; i<n; ++i) if(ecc[i] == rad) centers.push_back(i);
        
        int ec = 0;
        for(int i=0; i<n; ++i) {
            int md = 1e9;
            for(int c : centers) md = min(md, dist[i][c]);
            ec = max(ec, md);
        }
        
        // 2. Girth
        int g = 1e9;
        for(int i=0; i<n; ++i) {
            vector<int> d(n, 1e9);
            vector<int> p(n, -1);
            d[i] = 0;
            queue<int> q; q.push(i);
            while(!q.empty()) {
                int u = q.front(); q.pop();
                for(int v=0; v<n; ++v) {
                    if(adj[u][v]) {
                        if(d[v] == 1e9) {
                            d[v] = d[u] + 1;
                            p[v] = u;
                            q.push(v);
                        } else if(p[u] != v) {
                            g = min(g, d[u] + d[v] + 1);
                        }
                    }
                }
            }
        }
        if(g > 1e8) g = 0; // acyclic
        
        int rhs = g - 1 + ec;
        
        // 3. Tree number
        // A subset is an induced tree if it is connected and has |S|-1 edges
        int max_tree = 0;
        for(int mask = 1; mask < (1 << n); ++mask) {
            int size = __builtin_popcount(mask);
            if(size <= max_tree) continue;
            
            int edges = 0;
            for(int i=0; i<n; ++i) {
                if((mask >> i) & 1) {
                    for(int j=i+1; j<n; ++j) {
                        if(((mask >> j) & 1) && adj[i][j]) {
                            edges++;
                        }
                    }
                }
            }
            if(edges != size - 1) continue;
            
            // check connectivity
            int start = -1;
            for(int i=0; i<n; ++i) if((mask >> i) & 1) { start = i; break; }
            
            vector<int> vis(n, 0);
            queue<int> q;
            q.push(start);
            vis[start] = 1;
            int comp_size = 0;
            while(!q.empty()) {
                int u = q.front(); q.pop();
                comp_size++;
                for(int v=0; v<n; ++v) {
                    if(adj[u][v] && ((mask >> v) & 1) && !vis[v]) {
                        vis[v] = 1;
                        q.push(v);
                    }
                }
            }
            if(comp_size == size) {
                max_tree = max(max_tree, size);
                if (max_tree >= rhs) break; // Optimization! We only care if max_tree < rhs
            }
        }
        
        if(max_tree < rhs) {
            cout << "Counterexample: " << line << " tree=" << max_tree << " g=" << g << " ec=" << ec << " rhs=" << rhs << endl;
            return 0; // Exit on first counterexample
        }
    }
    return 0;
}
