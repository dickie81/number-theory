#!/usr/bin/env python3
"""Write docs/inventory.md, the inventory of the library's results, from the sources alone (no build needed).

    python3 scripts/inventory.py           # write docs/inventory.md
    python3 scripts/inventory.py --check   # exit 1 if docs/inventory.md is not what this script writes
    python3 scripts/inventory.py --json    # the inventory as JSON, on standard output

The inventory lists the theorems whose axioms lib/check/CheckAll.lean (the library's final results) and
lib/check/Check.lean (the papers' theorems) print, module by module: each with the headline of its docstring (its bold
title, or else its first sentence), whether it is a paper's, and the note of formalisations/ that names it, if one does.
It then lists the modules that neither Check nor CheckAll imports, directly or not, with their headline theorems,
those whose docstring opens with a bold title. Modules, layers and imports are read as import_cone.py reads them.
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_cone  # noqa: E402

ROOT = import_cone.ROOT
OUT = os.path.join(ROOT, "docs", "inventory.md")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:(\[{]+)")


def declarations(path):
    """The declarations of a module, in order: (full name, kind, docstring or None, index of its line)."""
    lines = open(path, encoding="utf-8").read().split("\n")
    out, namespaces, doc, i = [], [], None, 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"namespace\s+(\S+)", line)
        if m:
            namespaces.append(m.group(1))
        elif re.match(r"end\s+(\S+)\s*$", line) and namespaces and line.split()[1] == namespaces[-1]:
            namespaces.pop()
        elif line.lstrip().startswith("/--"):
            j = i
            while "-/" not in lines[j][lines[j].index("/--") + 3 if j == i else 0:] and j + 1 < len(lines):
                j += 1
            doc = " ".join(x.strip() for x in lines[i:j + 1])
            i = j
        elif DECL.match(line):
            kind, name = DECL.match(line).groups()
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(namespaces + [name])
            out.append((full, kind, doc, i))
            doc = None
        elif line.strip() and not line.startswith(("@[", " ", "--", "open ")):
            doc = None
        i += 1
    return out


def headline(doc):
    """A docstring's bold title, or else its first sentence."""
    if not doc:
        return ""
    text = " ".join(doc.replace("/--", "", 1).rsplit("-/", 1)[0].split())
    m = re.match(r"\*\*(.+?)\*\*", text)
    if m:
        return m.group(1).rstrip(":.")
    m = re.match(r"(.+?[.:])(?:\s|$)", text)
    first = m.group(1).rstrip(":") if m else text
    return first if len(first) <= 160 else first[:157].rsplit(" ", 1)[0] + "…"


def title(path):
    """The first heading of a module's header comment, or ''."""
    text = open(path, encoding="utf-8").read()
    m = re.search(r"/-!?(.*?)-/", text, re.S)
    h = re.search(r"^\s*#\s+(.+)$", m.group(1), re.M) if m else None
    return h.group(1).strip() if h else ""


def notes():
    """The note of formalisations/ for each full name: the one whose row of the index names it in its Lean column,
    or else the first note that mentions it."""
    out, d = {}, os.path.join(ROOT, "formalisations")
    for row in open(os.path.join(d, "README.md"), encoding="utf-8").read().splitlines():
        cells = [c.strip() for c in re.split(r"(?<!\\)\|", row)[1:-1]]
        link = re.search(r"\]\(([\w-]+\.md)\)", cells[-1]) if len(cells) == 5 else None
        if link:
            for name in re.findall(r"`([A-Za-z_][\w.']*\.[\w.']+)`", cells[2]):
                out.setdefault(name, link.group(1))
    for f in sorted(os.listdir(d)):
        if f.endswith(".md") and f != "README.md":
            for name in re.findall(r"`([A-Za-z_][\w.']*\.[\w.']+)`", open(os.path.join(d, f), encoding="utf-8").read()):
                out.setdefault(name, f)
    return out


def printed(name):
    path = os.path.join(ROOT, "lib", "check", name + ".lean")
    return re.findall(r"^#print axioms (\S+)", open(path, encoding="utf-8").read(), re.M)


def inventory():
    mods, imports = import_cone.sources()
    decls = {m: declarations(os.path.join(ROOT, p)) for m, p in mods.items()}
    where = {full: m for m, ds in decls.items() for full, *_ in ds}
    check, named = printed("Check"), notes()
    listed = printed("CheckAll") + [n for n in check if n not in set(printed("CheckAll"))]
    check = set(check)
    reached = import_cone.cone(imports, ["Check"]) | import_cone.cone(imports, ["CheckAll"])
    layer = {m: mods[m].split(os.sep)[1] for m in mods}
    results = {}
    missing = sorted(set(listed) - set(where))
    if missing:
        sys.exit("Check or CheckAll prints names that no module declares: " + ", ".join(missing[:5]))
    for full in listed:
        results.setdefault(where[full], set()).add(full)
    entries = []
    for m in sorted(mods, key=lambda m: (import_cone.DIRS.index(layer[m]), m)):
        if m in results:
            rows = [{"name": f, "headline": headline(doc), "paper": f in check, "note": named.get(f)}
                    for f, _, doc, _ in decls[m] if f in results[m]]
            entries.append({"module": m, "layer": layer[m], "path": mods[m], "title": title(os.path.join(ROOT, mods[m])),
                            "printed": True, "results": rows})
        elif m not in reached:
            rows = [{"name": f, "headline": headline(doc), "paper": False, "note": named.get(f)}
                    for f, kind, doc, _ in decls[m] if kind in ("theorem", "lemma") and doc and doc.startswith("/-- **")]
            entries.append({"module": m, "layer": layer[m], "path": mods[m], "title": title(os.path.join(ROOT, mods[m])),
                            "printed": False, "results": rows})
    return entries


def markdown(entries):
    inside = [e for e in entries if e["printed"]]
    outside = [e for e in entries if not e["printed"]]
    n_res = sum(len(e["results"]) for e in inside)
    n_paper = sum(r["paper"] for e in inside for r in e["results"])
    out = ["# Inventory of the library's results", "",
           "Written by `scripts/inventory.py` from the sources; do not edit it by hand. `python3 scripts/inventory.py`",
           "rewrites it, and CI checks that it is current (`--check`).", "",
           f"`lib/check/CheckAll.lean` and `lib/check/Check.lean` print the axioms of {n_res} theorems: the library's final",
           f"results and the papers' theorems, of which there are {n_paper}, marked *paper*. Each line gives a theorem's",
           "name and the headline of its docstring, and links the note of `formalisations/` that names it, if one does.",
           f"The last section lists the {len(outside)} modules that neither `Check` nor `CheckAll` imports, directly or",
           "not, with their headline theorems (those whose docstring opens with a bold title).",
           "", "| Layer | Modules with results | Results | Modules outside both | Their headline theorems |",
           "|---|---|---|---|---|"]
    for d in import_cone.DIRS[:-1]:
        a = [e for e in inside if e["layer"] == d]
        b = [e for e in outside if e["layer"] == d]
        out.append(f"| `lib/{d}` | {len(a)} | {sum(len(e['results']) for e in a)} | {len(b)} | "
                   f"{sum(len(e['results']) for e in b)} |")

    def section(es, heading):
        out.extend(["", f"## {heading}"])
        for d in import_cone.DIRS:
            es_d = [e for e in es if e["layer"] == d]
            if not es_d:
                continue
            out.extend(["", f"### `lib/{d}`"])
            for e in es_d:
                out.extend(["", f"#### `{e['module']}`" + (f": {e['title']}" if e["title"] else "")])
                if e["results"]:
                    out.append("")
                for r in e["results"]:
                    marks = (" *paper*" if r["paper"] else "") + \
                            (f" ([note](../formalisations/{r['note']}))" if r["note"] else "")
                    out.append(f"- `{r['name']}`" + (f": {r['headline']}" if r["headline"] else "") + marks)

    section(inside, "The results of `CheckAll`")
    section(outside, "Modules outside `Check` and `CheckAll`")
    return "\n".join(out) + "\n"


def main(argv):
    entries = inventory()
    if "--json" in argv:
        print(json.dumps(entries, ensure_ascii=False, indent=1))
        return 0
    text = markdown(entries)
    if "--check" in argv:
        current = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        ok = current == text
        print("docs/inventory.md is current" if ok else
              "docs/inventory.md is not current: run python3 scripts/inventory.py")
        return 0 if ok else 1
    open(OUT, "w", encoding="utf-8").write(text)
    print(f"wrote docs/inventory.md: {text.count(chr(10))} lines")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
