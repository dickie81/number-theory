#!/usr/bin/env python3
"""Compare two environments at the level of the kernel, from the fingerprints that `lean/Fingerprint.lean` writes.

    python3 -I tools/rh/fp_compare.py OLD.tsv NEW.tsv [--renamed R.tsv] [--notwin N.txt] [ROOT ...]

Each constant gets a deep hash: of its kind, of the shape of its type and of the deep hashes of the constants that
the type names, in order; and the same for its value, unless it is a theorem (a proof is not part of what a
theorem means), an axiom or an opaque constant. Two constants with the same deep hash are the same term over the
same constants all the way down, whatever they are called: an old constant has a twin when some new constant has
its deep hash. A term that mentions only constants with twins means the same in both environments, once names are
replaced by the twins' names.

Constants that name each other (an inductive type and its constructors) are hashed together, by refinement.

For each ROOT the script says whether it has a twin, and if not lists the first causes: the constants that it rests
on, that have no twin, and that rest only on constants with twins.

With `--by-name` the question is weaker, and it is the one that matters for carrying a proof over: can a term name
this constant in the new environment and still be read the same way? A constant keeps its name when the new
environment has a constant of that name, of the same kind, whose type has the same shape and names the same
constants, and every constant that the type names keeps its name (for an inductive type, its constructors too).
The values of definitions are not compared: whether a changed definition still unfolds as a proof needs is for the
new kernel to say. `--notwin` then lists the constants that do not keep their name.
"""
import argparse
import hashlib
import json
import sys
from collections import Counter, deque

SEP = "\x1f"
VALUE_KINDS = ("d", "i", "c", "r")


def h(*parts):
    return int.from_bytes(hashlib.blake2b(repr(parts).encode(), digest_size=8).digest(), "big")


class Env:
    def __init__(self, path):
        self.name, self.idx, self.rec = [], {}, []
        with open(path, encoding="utf-8") as f:
            for line in f:
                p = line.rstrip("\n").split("\t")
                if len(p) != 8:
                    continue
                self.idx[p[0]] = len(self.name)
                self.name.append(p[0])
                self.rec.append(p)
        n = len(self.name)
        self.kind = [r[1] for r in self.rec]
        self.ty, self.val = [None] * n, [None] * n
        missing = 0
        for i, r in enumerate(self.rec):
            ty, val = [], []
            for src, dst in ((r[5], ty), (r[7] if r[1] in VALUE_KINDS else "", val)):
                for name in src.split(SEP) if src else ():
                    j = self.idx.get(name)
                    if j is None:
                        missing += 1
                        j = -1 - (h(name) % (1 << 40))
                    dst.append(j)
            self.ty[i], self.val[i] = ty, val
        self.missing = missing
        self.deep = self.hashes()

    def sccs(self):
        """Tarjan's algorithm, without recursion. Components come out with what they reach first."""
        n = len(self.name)
        index, low, on = [-1] * n, [0] * n, bytearray(n)
        stack, out, counter = [], [], 0
        for root in range(n):
            if index[root] != -1:
                continue
            work = [(root, 0)]
            while work:
                v, i = work[-1]
                if i == 0:
                    index[v] = low[v] = counter
                    counter += 1
                    stack.append(v)
                    on[v] = 1
                succ = self.ty[v] + self.val[v]
                advanced = False
                while i < len(succ):
                    w = succ[i]
                    i += 1
                    if w < 0:
                        continue
                    if index[w] == -1:
                        work[-1] = (v, i)
                        work.append((w, 0))
                        advanced = True
                        break
                    if on[w]:
                        low[v] = min(low[v], index[w])
                if advanced:
                    continue
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = stack.pop()
                        on[w] = 0
                        comp.append(w)
                        if w == v:
                            break
                    out.append(comp)
        return out

    def hashes(self):
        deep = [0] * len(self.name)
        for comp in self.sccs():
            if len(comp) == 1 and comp[0] not in self.ty[comp[0]] and comp[0] not in self.val[comp[0]]:
                v = comp[0]
                r = self.rec[v]
                deep[v] = h(r[1], r[2], r[3], r[4], tuple(deep[w] if w >= 0 else w for w in self.ty[v]),
                            r[6] if r[1] in VALUE_KINDS else 0, tuple(deep[w] if w >= 0 else w for w in self.val[v]))
                continue
            inside = set(comp)
            cur = {}
            for v in comp:
                r = self.rec[v]
                cur[v] = h(r[1], r[2], r[3], r[4], tuple("in" if w in inside else (deep[w] if w >= 0 else w) for w in self.ty[v]),
                           r[6], tuple("in" if w in inside else (deep[w] if w >= 0 else w) for w in self.val[v]))
            for _ in range(min(len(comp), 12) + 1):
                cur = {v: h(cur[v], tuple(cur[w] for w in self.ty[v] if w in inside),
                            tuple(cur[w] for w in self.val[v] if w in inside)) for v in comp}
            for v in comp:
                deep[v] = cur[v]
        return deep


def read(path):
    out = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if len(p) == 8:
                out[p[0]] = p
    return out


def by_name(args):
    old, new = read(args.old), read(args.new)
    seeds = {}
    for name, r in old.items():
        o = new.get(name)
        if o is None:
            seeds[name] = "gone"
        elif (o[1] == "t") != (r[1] == "t") and {o[1], r[1]} != {"d", "t"}:
            seeds[name] = "kind"
        elif o[1] != r[1] and not {o[1], r[1]} <= {"d", "t", "o"}:
            seeds[name] = "kind"
        elif o[2] != r[2] or o[4] != r[4] or o[5] != r[5]:
            seeds[name] = "type"
        elif r[1] in ("i", "c", "r") and (o[3] != r[3] or o[6] != r[6] or o[7] != r[7]):
            seeds[name] = "shape"
    users = {}
    for name, r in old.items():
        refs = r[5].split(SEP) if r[5] else []
        if r[1] in ("i", "c", "r") and r[7]:
            refs = refs + r[7].split(SEP)
        for x in refs:
            users.setdefault(x, []).append(name)
    bad = set(seeds)
    queue = deque(seeds)
    while queue:
        x = queue.popleft()
        for u in users.get(x, ()):
            if u not in bad:
                bad.add(u)
                queue.append(u)
    n = len(old)
    print("old: %d constants; new: %d" % (n, len(new)))
    print("first causes: %d (%s)" % (len(seeds), ", ".join("%s %d" % kv for kv in Counter(seeds.values()).most_common())))
    print("first causes by kind:", Counter(old[x][1] + ":" + why for x, why in seeds.items()).most_common(12))
    print("do not keep their name: %d of %d (%.1f%%); by kind: %s"
          % (len(bad), n, 100.0 * len(bad) / n, Counter(old[x][1] for x in bad).most_common()))
    if args.notwin:
        with open(args.notwin, "w", encoding="utf-8") as f:
            for name in sorted(bad):
                f.write(name + "\n")
    if args.renamed:
        open(args.renamed, "w").close()
    for root in args.roots:
        if root not in old:
            print("\n%s: not in the old environment" % root)
            continue
        cone, queue = {root}, deque([root])
        while queue:
            r = old[queue.popleft()]
            refs = (r[5].split(SEP) if r[5] else []) + (r[7].split(SEP) if r[7] and r[1] != "t" else [])
            for x in refs:
                if x in old and x not in cone:
                    cone.add(x)
                    queue.append(x)
        first = sorted(x for x in cone if x in seeds)
        print("\n%s: %s; what it means rests on %d constants, %d of them do not keep their name, %d first causes"
              % (root, "does NOT keep its name" if root in bad else "keeps its name", len(cone),
                 sum(1 for x in cone if x in bad), len(first)))
        for x in first[:args.show]:
            print("   %-6s %s %s" % (seeds[x], old[x][1], x))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old")
    ap.add_argument("new")
    ap.add_argument("roots", nargs="*")
    ap.add_argument("--renamed", help="write the old names whose twin has another name: `old<TAB>new` lines")
    ap.add_argument("--notwin", help="write the old names with no twin, one a line")
    ap.add_argument("--show", type=int, default=40)
    ap.add_argument("--by-name", action="store_true")
    args = ap.parse_args()
    if args.by_name:
        return by_name(args)
    old, new = Env(args.old), Env(args.new)
    twin = {}
    for i, d in enumerate(new.deep):
        # of several new constants with one hash, prefer the one with the old name: found below by name first
        twin.setdefault(d, i)
    new_by_name = new.idx
    has, same_name, renamed = bytearray(len(old.name)), 0, {}
    for i, d in enumerate(old.deep):
        j = new_by_name.get(old.name[i])
        if j is not None and new.deep[j] == d:
            has[i] = 1
            same_name += 1
        elif d in twin:
            has[i] = 1
            renamed[old.name[i]] = new.name[twin[d]]
    n = len(old.name)
    print("old: %d constants (%d names not found); new: %d" % (n, old.missing, len(new.name)))
    print("with a twin: %d (%.1f%%), of them %d under another name; without: %d"
          % (sum(has), 100.0 * sum(has) / n, len(renamed), n - sum(has)))
    print("without a twin, by kind:", Counter(old.kind[i] for i in range(n) if not has[i]).most_common())
    if args.renamed:
        with open(args.renamed, "w", encoding="utf-8") as f:
            for a, b in renamed.items():
                f.write("%s\t%s\n" % (a, b))
    if args.notwin:
        with open(args.notwin, "w", encoding="utf-8") as f:
            for i in range(n):
                if not has[i]:
                    f.write(old.name[i] + "\n")
    for root in args.roots:
        r = old.idx.get(root)
        if r is None:
            print("\n%s: not in the old environment" % root)
            continue
        cone, queue = {r}, deque([r])
        while queue:
            v = queue.popleft()
            for w in old.ty[v] + old.val[v]:
                if w >= 0 and w not in cone:
                    cone.add(w)
                    queue.append(w)
        bad = [v for v in cone if not has[v]]
        first = sorted(old.name[v] for v in bad if all(w < 0 or has[w] for w in old.ty[v] + old.val[v]))
        print("\n%s: %s; rests on %d constants, %d without a twin, %d first causes"
              % (root, "has a twin" if has[r] else "NO twin", len(cone), len(bad), len(first)))
        for name in first[:args.show]:
            v = old.idx[name]
            j = new_by_name.get(name)
            why = "gone" if j is None else ("kind" if new.kind[j] != old.kind[v] else
                                            ("type" if new.rec[j][4] != old.rec[v][4] or len(new.ty[j]) != len(old.ty[v])
                                             else "value"))
            print("   %-6s %s %s" % (why, old.kind[v], name))


if __name__ == "__main__":
    main()
