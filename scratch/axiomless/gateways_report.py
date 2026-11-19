#!/usr/bin/env python3
"""Print the dominator tree that gateways.c computes, with names.

    python3 gateways_report.py CENSUS.tsv DOM.txt [MIN_SHARE]

Each line: the share of the counted theorems that depend on the axiom only through this constant, the count, and the
constant, indented under its immediate dominator. Only constants with at least MIN_SHARE percent (default 1) print.
"""
import sys
from collections import defaultdict

def main():
    tsv, dom = sys.argv[1], sys.argv[2]
    min_share = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    names = [l.split("\t", 1)[0] for l in open(tsv, encoding="utf-8") if not l.startswith("#axiom")]
    rows = [tuple(map(int, l.split())) for l in open(dom)]
    count = {v: c for c, v, _, _ in rows}
    children = defaultdict(list)
    root = None
    for c, v, d, _ in rows:
        if v == d:
            root = v
        else:
            children[d].append(v)
    total = count[root]
    def show(v, depth):
        share = 100 * count[v] / total
        if share < min_share:
            return
        print(f"{'  ' * depth}{share:5.1f}%  {count[v]:7d}  {names[v]}")
        for c in sorted(children[v], key=lambda c: -count[c]):
            show(c, depth + 1)
    show(root, 0)

if __name__ == "__main__":
    main()
