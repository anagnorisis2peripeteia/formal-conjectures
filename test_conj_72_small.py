import sys
import networkx as nx
import test_conj_72

def main():
    for line in sys.stdin:
        line = line.strip()
        if not line: continue
        G = nx.from_graph6_bytes(line.encode('ascii'))
        if test_conj_72.check_72(G):
            print(f"Found counterexample: {line}")
            sys.exit(0)

if __name__ == '__main__':
    main()
