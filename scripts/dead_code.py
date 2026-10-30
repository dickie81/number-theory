#!/usr/bin/env python3
"""The dead-code check: the library keeps no declaration that its results do not use, and every result is a paper's,
the site's, or registered in formalisations/.

    python3 scripts/dead_code.py               # after `lake build Check CheckAll CheckZeta23 CheckDH deadcode`
    python3 scripts/dead_code.py --json OUT    # also write the findings, with each declaration's lines, to OUT

The roots are the theorems that the check files lib/check/*.lean print. `lake exe deadcode` (scripts/lean/DeadCode.lean)
imports the check files, Check, CheckAll and CheckDH together, then CheckZeta23, which they cannot import, and walks what
the roots use, through types and proofs. The check fails if:

1. a declaration of lib/core, lib/pnt, lib/dh, lib/zeta23 or lib/check is used by no root (Lean's generated
   declarations and the meta level, macros and syntax, aside), or a module of those directories is imported by no
   check file;
2. a root has a closed hypothesis, a proposition or an instance that mentions none of its variables (such as
   `RiemannHypothesis`, `SieveRoute.TypeIIAt` or `[SieveCert.Grid]`), and no root without one uses it, nor a result of
   the section "Conditional results" of formalisations/README.md, which lists the results conditional on purpose: a
   lemma of a route that nothing proves any more;
3. a root that no other root uses, a result of the library, is neither printed by Check.lean (the papers' results),
   nor presented by the page on the zeros (scripts/zeros_page.py), nor named in formalisations/: a result that
   nothing uses must be registered there, with what it is;
4. a result of "Conditional results" is printed by no check file, or a check file prints a name that no module of its
   environment declares.
"""
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import zeros_page  # noqa: E402

DIRS = ["core", "pnt", "dh", "zeta23", "check"]
# the environments: the check files that can be imported together
RUNS = [["Check", "CheckAll", "CheckDH"], ["CheckZeta23"]]
NAME = r"`([A-Za-z_][\w.']*\.[\w.']+)`"


def modules(d):
    return sorted(f[:-5] for f in os.listdir(os.path.join(ROOT, "lib", d)) if f.endswith(".lean"))


def printed(check):
    text = open(os.path.join(ROOT, "lib", "check", check + ".lean"), encoding="utf-8").read()
    return re.findall(r"^#print axioms (\S+)", text, re.M)


def registry():
    """The names that formalisations/ registers, and those of the Lean column of its table "Conditional results"."""
    d = os.path.join(ROOT, "formalisations")
    names = set()
    for f in sorted(os.listdir(d)):
        if f.endswith(".md"):
            names |= set(re.findall(NAME, open(os.path.join(d, f), encoding="utf-8").read()))
    readme = open(os.path.join(d, "README.md"), encoding="utf-8").read()
    m = re.search(r"^## Conditional results\n(.*?)(?=^## |\Z)", readme, re.M | re.S)
    conditional = set()
    for row in (m.group(1) if m else "").splitlines():
        cells = re.split(r"(?<!\\)\|", row)[1:-1]
        if len(cells) == 3:
            conditional |= set(re.findall(NAME, cells[2]))
    return names, conditional


def page():
    """The theorems that the page on the zeros presents."""
    out = set()

    def walk(o):
        if isinstance(o, str):
            out.update(re.findall(r"[A-Z][\w']*\.[\w.']+", o))
        elif isinstance(o, dict):
            for v in o.values():
                walk(v)
        elif isinstance(o, (list, tuple)):
            for v in o:
                walk(v)
    walk(zeros_page.extract())
    return out


def run(tmp, imports):
    r = subprocess.run(["lake", "exe", "deadcode", os.path.join(tmp, "ours"), os.path.join(tmp, "roots"),
                        os.path.join(tmp, "allow")] + imports, cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"deadcode {' '.join(imports)} failed:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    return json.loads(r.stdout.strip().splitlines()[-1])


def analyse(runs):
    """The findings of the runs, merged: a declaration is unused if no run that imports its module reaches it, and a
    root is used if a run finds a use of it."""
    present = [set(r["ours"]) for r in runs]
    # keyed by module too: two modules can have private declarations of the same name
    dead = [{(d["module"], d["name"]): d for d in r["dead"]} for r in runs]
    unused = []
    for key in sorted(set().union(*dead)):
        if all(key in ds for ds, mods in zip(dead, present) if key[0] in mods):
            unused.append(next(ds[key] for ds in dead if key in ds))
    roots = {}
    for r in runs:
        for x in r["roots"]:
            e = roots.setdefault(x["name"], dict(x, usedBy=None, usedByAny=None))
            e["usedBy"] = e["usedBy"] or x["usedBy"]
            e["usedByAny"] = e["usedByAny"] or x["usedByAny"]
    # for each module: its declarations, the most that one run reaches, and its macros, syntax and elaborators
    stats = {}
    for r in runs:
        for m, (total, alive, metas) in r["stats"].items():
            e = stats.setdefault(m, [total, 0, metas])
            e[1] = max(e[1], alive)
    return unused, roots, set().union(*present), stats


def main():
    ours = [m for d in DIRS for m in modules(d)]
    checks = [c for run_ in RUNS for c in run_]
    prints = {c: printed(c) for c in checks}
    roots = sorted({n for c in checks for n in prints[c]})
    registered, conditional = registry()
    shown = page()
    with tempfile.TemporaryDirectory() as tmp:
        for name, items in (("ours", ours), ("roots", roots), ("allow", sorted(conditional))):
            open(os.path.join(tmp, name), "w", encoding="utf-8").write("\n".join(items) + "\n")
        runs = [run(tmp, imports) for imports in RUNS]
    unused, info, imported, stats = analyse(runs)
    unimported = sorted(set(ours) - imported)
    condUnused = sorted((x for x in info.values() if x["closed"] and x["name"] not in conditional and not x["usedBy"]),
                        key=lambda x: x["name"])
    unregistered = sorted(n for n, x in info.items() if not x["usedByAny"] and n not in prints["Check"]
                          and n not in shown and n not in registered)
    stale = sorted(conditional - set(roots))
    missing = sorted(set(roots) - set(info))
    byMod = {}
    for d in unused:
        byMod.setdefault(d["module"], []).append(d)
    for m in sorted(byMod):
        names = [d["name"] for d in byMod[m]]
        print(f"{m}: {len(names)} unused: " + ", ".join(names[:12]) + (" …" if len(names) > 12 else ""))
    for m in unimported:
        print(f"{m}: imported by no check file")
    for x in condUnused:
        print(f"{x['name']} ({x['module']}): printed, with the closed hypotheses {', '.join(x['closed'][:3])}, "
              f"and used by no result")
    for n in unregistered:
        print(f"{n}: a result that nothing uses, neither a paper's, nor on the page on the zeros, nor in "
              f"formalisations/")
    for n in stale:
        print(f"{n}: in formalisations/README.md's Conditional results but printed by no check file")
    for n in missing:
        print(f"{n}: printed by a check file, but no module of its environment declares it")
    ok = not (unused or unimported or condUnused or unregistered or stale or missing)
    print(f"dead_code: {len(roots)} printed theorems; {len(unused)} unused declarations in {len(byMod)} modules, "
          f"{len(unimported)} modules imported by no check file, {len(condUnused)} conditional theorems that no "
          f"result uses, {len(unregistered)} unregistered results")
    print("DEAD CODE PASS" if ok else "DEAD CODE FAIL")
    if "--json" in sys.argv:
        json.dump({"unused": unused, "unimported": unimported, "conditionalUnused": condUnused,
                   "unregistered": unregistered, "stale": stale, "missing": missing, "roots": info, "modules": stats},
                  open(sys.argv[sys.argv.index("--json") + 1], "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
