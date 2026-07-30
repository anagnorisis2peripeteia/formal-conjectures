#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 20

int read_graph6(char *g6, int *n, int adj[MAXN][MAXN]) {
    *n = g6[0] - 63;
    if (*n <= 0 || *n > MAXN) return 0;
    for (int i = 0; i < *n; i++)
        for (int j = 0; j < *n; j++)
            adj[i][j] = 0;
    int k = 1;
    int bit_idx = 0;
    int val = g6[k] - 63;
    for (int j = 1; j < *n; j++) {
        for (int i = 0; i < j; i++) {
            if (val & (1 << (5 - bit_idx))) {
                adj[i][j] = 1;
                adj[j][i] = 1;
            }
            bit_idx++;
            if (bit_idx == 6) {
                k++;
                val = g6[k] - 63;
                bit_idx = 0;
            }
        }
    }
    return 1;
}

int path_closure(int n, int adj[MAXN][MAXN]) {
    int current[MAXN][MAXN];
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            current[i][j] = adj[i][j];
            
    while (1) {
        int added = 0;
        int deg[MAXN] = {0};
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (current[i][j]) deg[i]++;
                
        for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
                if (!current[i][j] && deg[i] + deg[j] >= n - 1) {
                    current[i][j] = 1;
                    current[j][i] = 1;
                    added = 1;
                }
            }
        }
        if (!added) break;
    }
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (!current[i][j]) return 0;
    return 1;
}

int is_exception_11(int deg[MAXN]) {
    // Check against the 13 exception sequences for N=11
    int seqs[13][11] = {
        {6,6,6,6,6,6,6,4,4,4,2}, {6,6,6,6,6,6,6,4,4,3,3}, {6,6,6,6,6,6,6,3,3,3,3},
        {6,6,6,6,6,6,5,4,4,4,3}, {6,6,6,6,6,6,5,4,3,3,3}, {6,6,6,6,6,6,4,4,4,4,4},
        {6,6,6,6,6,6,4,4,4,3,3}, {6,6,6,6,6,5,5,4,4,3,3}, {6,6,6,6,6,5,4,4,4,4,3},
        {6,6,6,6,6,4,4,4,4,4,4}, {6,6,6,6,5,5,5,4,4,4,3}, {6,6,6,6,5,5,4,4,4,4,4},
        {5,5,5,5,5,5,4,4,4,4,4}
    };
    for (int i = 0; i < 13; i++) {
        int match = 1;
        for (int j = 0; j < 11; j++) {
            if (deg[j] != seqs[i][j]) { match = 0; break; }
        }
        if (match) return 1;
    }
    return 0;
}

int is_exception_12(int deg[MAXN]) {
    // Check against the 14 exception sequences for N=12
    int seqs[14][12] = {
        {6,6,6,6,6,6,6,6,4,4,4,4}, {6,6,6,6,6,6,6,5,5,5,5,4}, {6,6,6,6,6,6,6,5,5,5,4,3},
        {6,6,6,6,6,6,6,5,5,4,4,4}, {6,6,6,6,6,6,6,4,4,4,4,4}, {6,6,6,6,6,6,5,5,5,5,5,5},
        {6,6,6,6,6,6,5,5,5,5,5,3}, {6,6,6,6,6,6,5,5,5,5,4,4}, {6,6,6,6,6,6,5,5,4,4,4,4},
        {6,6,6,6,6,5,5,5,5,5,5,4}, {6,6,6,6,6,5,5,5,5,4,4,4}, {6,6,6,6,5,5,5,5,5,5,5,5},
        {6,6,6,6,5,5,5,5,5,5,4,4}, {6,6,6,5,5,5,5,5,5,5,5,4}
    };
    for (int i = 0; i < 14; i++) {
        int match = 1;
        for (int j = 0; j < 12; j++) {
            if (deg[j] != seqs[i][j]) { match = 0; break; }
        }
        if (match) return 1;
    }
    return 0;
}

void sort_desc(int *arr, int n) {
    for (int i=0; i<n-1; i++) {
        for (int j=i+1; j<n; j++) {
            if (arr[j] > arr[i]) {
                int t = arr[i]; arr[i] = arr[j]; arr[j] = t;
            }
        }
    }
}

int main(int argc, char **argv) {
    char line[1024];
    long long count = 0;
    long long non_closing = 0;
    long long exc_graphs = 0;
    int n;
    int adj[MAXN][MAXN];
    
    while (fgets(line, sizeof(line), stdin)) {
        size_t len = strlen(line);
        if (len > 0 && line[len-1] == '\n') line[len-1] = '\0';
        if (len > 0 && line[len-2] == '\r') line[len-2] = '\0';
        
        if (!read_graph6(line, &n, adj)) continue;
        count++;
        
        int deg[MAXN] = {0};
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                if (adj[i][j]) deg[i]++;
        
        sort_desc(deg, n);
        
        int is_exc = 0;
        if (n == 11) is_exc = is_exception_11(deg);
        else if (n == 12) is_exc = is_exception_12(deg);
        
        if (is_exc) {
            exc_graphs++;
            if (!path_closure(n, adj)) {
                non_closing++;
                printf("NON-CLOSING EXC: n=%d, %s\n", n, line);
            }
        }
        
        if (count % 10000000 == 0) {
            fprintf(stderr, "Processed %lld graphs...\n", count);
        }
    }
    
    printf("Total: %lld, Exc graphs: %lld, Non-closing exc: %lld\n", count, exc_graphs, non_closing);
    return 0;
}
