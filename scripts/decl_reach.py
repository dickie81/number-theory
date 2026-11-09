#!/usr/bin/env python3
"""Can one declaration's proof reach another? A static over-approximation from the sources, no build needed.
    python3 scripts/decl_reach.py ROOT_MODULE START TARGET
e.g. python3 scripts/decl_reach.py LinnikCGLDensity LinnikCGLDensity.cglDensity Eis.LFunction_ne_zero_of_re_gt

It takes the import cone of ROOT_MODULE (scripts/import_cone.py), strips comments and docstrings, splits each module
into declarations (with their namespaces), and links a declaration to every declaration of the cone whose last name
component equals the last component of an identifier in its text. Reachability from START over these links
over-approximates the constants START's proof can use, so "not reachable" means START does not use TARGET. The
blind spots are uses that leave no identifier in the source: simp sets, instances and other attribute-driven
tactics (check that TARGET's module and its users declare none), and the vendored libraries and Mathlib, which are
leaves here. "Reachable" proves nothing; it prints one chain to inspect.
"""
import collections
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAYERS = ["lib/core", "lib/pnt", "lib/dh", "lib/zeta23", "lib/check"]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|scoped)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|irreducible_def)\s+([^\s:({\[]+)")
TOK = re.compile(r"[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'₀-ₜͰ-Ͽ.]*")


def strip_comments(t):
    out, i, depth = [], 0, 0
    while i < len(t):
        if t.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and t.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if t[i] == "\n" else ""); i += 1; continue
        if t.startswith("--", i):
            j = t.find("\n", i); i = len(t) if j < 0 else j; continue
        out.append(t[i]); i += 1
    return "".join(out)


def main():
    root, start, target = sys.argv[1:4]
    r = subprocess.run([sys.executable, os.path.join(ROOT, "scripts", "import_cone.py"), root, "--all-modules"],
                       capture_output=True, text=True, cwd=ROOT)
    mods = sorted({w for w in re.split(r"[\s,]+", r.stdout) if re.fullmatch(r"[A-Z][A-Za-z0-9]+", w)})
    decls, body = {}, collections.defaultdict(list)
    for m in mods:
        path = next((os.path.join(ROOT, d, m + ".lean") for d in LAYERS
                     if os.path.exists(os.path.join(ROOT, d, m + ".lean"))), None)
        if not path:
            continue
        ns, cur = [], None
        for s in strip_comments(open(path, encoding="utf-8").read()).split("\n"):
            mn = re.match(r"^namespace\s+(\S+)", s)
            if mn:
                ns.append(mn.group(1)); cur = None; continue
            me = re.match(r"^end\s+(\S+)", s)
            if me and ns and ns[-1] == me.group(1):
                ns.pop(); cur = None; continue
            md = DECL.match(s)
            if md:
                name = md.group(1)
                cur = name[7:] if name.startswith("_root_.") else ".".join(ns + [name])
                decls[cur] = m
            if cur:
                body[cur].append(s)
    bylast = collections.defaultdict(set)
    for d in decls:
        bylast[d.split(".")[-1]].add(d)
    edges = {}
    for d, lines in body.items():
        txt = lines[0].split(":", 1)[-1] + "\n" + "\n".join(lines[1:])
        toks = {t.split(".")[-1] for t in TOK.findall(txt)}
        edges[d] = set().union(*(bylast.get(t, set()) for t in toks)) - {d}
    print(f"{root}: {len(mods)} modules, {len(decls)} declarations")
    for name in (start, target):
        if name not in decls:
            print(f"{name} is not declared in the cone"); return 2
    prev, q = {start: None}, collections.deque([start])
    while q:
        u = q.popleft()
        for v in edges.get(u, ()):
            if v not in prev:
                prev[v] = u; q.append(v)
    print(f"{len(prev)} declarations reachable from {start}")
    if target in prev:
        path, v = [], target
        while v:
            path.append(v); v = prev[v]
        print("REACHABLE (a chain to inspect, not a proof of use):", " <- ".join(path))
        return 1
    print(f"NOT REACHABLE: {start} does not use {target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
