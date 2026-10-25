#!/usr/bin/env python3
"""The import cone of a module, from the sources alone (no build needed).

    python3 scripts/import_cone.py [ROOT ...]          # default root: Check, the default build target
    python3 scripts/import_cone.py ROOT --why MODULE   # the shortest chain of imports from ROOT to MODULE
    python3 scripts/import_cone.py ROOT --all-modules  # also list every module of the cone

It reads the `import` lines of lib/core, lib/pnt, lib/dh, lib/zeta23 and lib/check (the vendored libraries and
Mathlib are leaves). For each root it prints the number of modules and source bytes of the cone, by layer, and the
certificate part files (`lib/pnt/SieveCert<tag>P<k>.lean`, the heavy kernel checks) of the cone by certificate. Use it
before adding an `import` to a module that the default build reaches: one import of a module whose own cone holds a
certificate puts that certificate in the default build (`--why` shows the chain that does it).
"""
import collections
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIRS = ["core", "pnt", "dh", "zeta23", "check"]


def sources():
    mods = {}
    for d in DIRS:
        for f in os.listdir(os.path.join(ROOT, "lib", d)):
            if f.endswith(".lean"):
                mods[f[:-5]] = os.path.join("lib", d, f)
    imports = {}
    for m, p in mods.items():
        text = open(os.path.join(ROOT, p), encoding="utf-8").read()
        imports[m] = [i for i in re.findall(r"^import\s+(\S+)", text, re.M) if i in mods]
    return mods, imports


def cone(imports, roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m not in seen:
            seen.add(m)
            stack += imports[m]
    return seen


def why(imports, root, target):
    prev, queue = {root: None}, collections.deque([root])
    while queue:
        m = queue.popleft()
        for i in imports[m]:
            if i not in prev:
                prev[i] = m
                queue.append(i)
    if target not in prev:
        return None
    chain, m = [], target
    while m:
        chain.append(m)
        m = prev[m]
    return chain[::-1]


def main(argv):
    mods, imports = sources()
    args = [a for a in argv if not a.startswith("--")]
    roots = [a for a in args if a in mods]
    if "--why" in argv:
        target = argv[argv.index("--why") + 1]
        roots = [a for a in roots if a != target]
        chain = why(imports, roots[0] if roots else "Check", target)
        print(" -> ".join(chain) if chain else f"{target} is not in the import cone of {roots[0] if roots else 'Check'}")
        return 0
    roots = roots or ["Check"]
    for r in roots:
        c = cone(imports, [r])
        size = {m: os.path.getsize(os.path.join(ROOT, mods[m])) for m in c}
        layers = collections.Counter(mods[m].split(os.sep)[1] for m in c)
        certs = collections.Counter(re.sub(r"P\d+$", "", m) for m in c if re.fullmatch(r"SieveCert\w*P\d+", m))
        print(f"{r}: {len(c)} modules, {sum(size.values()) / 1e6:.2f} MB of source; by layer: "
              + ", ".join(f"{k} {v}" for k, v in sorted(layers.items())))
        print(f"  certificate part files: {sum(certs.values())}"
              + "".join(f"; {k}: {v}" for k, v in sorted(certs.items())))
        if "--all-modules" in argv:
            print("  " + " ".join(sorted(c)))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
