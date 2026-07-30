#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 20

// Reads graph6 format
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

int main(int argc, char **argv) {
    char line[1024];
    long long count = 0;
    long long non_closing = 0;
    int n;
    int adj[MAXN][MAXN];
    
    while (fgets(line, sizeof(line), stdin)) {
        size_t len = strlen(line);
        if (len > 0 && line[len-1] == '\n') line[len-1] = '\0';
        if (len > 0 && line[len-2] == '\r') line[len-2] = '\0';
        
        if (!read_graph6(line, &n, adj)) continue;
        
        count++;
        if (!path_closure(n, adj)) {
            non_closing++;
            printf("NON-CLOSING: %s\n", line);
        }
        
        if (count % 10000000 == 0) {
            fprintf(stderr, "Processed %lld graphs...\n", count);
        }
    }
    
    printf("Total: %lld, Non-closing: %lld\n", count, non_closing);
    return 0;
}
