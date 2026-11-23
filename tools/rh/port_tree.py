#!/usr/bin/env python3
"""The tree of the port: the library's files that a target imports, with the port's patches applied.

    python3 tools/rh/port_tree.py make TREE [--target FILE.lean] [--patches DIR] [--force]
    python3 tools/rh/port_tree.py save TREE [--patches DIR]
    python3 tools/rh/port_tree.py status TREE [--patches DIR]
    python3 tools/rh/port_tree.py errors TREE [--build OUT] [MODULE ...]

The library is written for the repository's pin of Lean and Mathlib. A port to another pin is a set of changes to
proofs, and it is kept as the library's vendored code is kept: as patches, one a file, beside the library and not
in it (`scratch/rh-claim/port/patches/<Module>.patch`). The statements are not to change; `status` lists the
changed lines that are not inside a proof as far as a pattern can tell, to be read by eye.

`make` copies every module that the target reaches by imports to TREE (`A/B.lean` for the module `A.B`), applies
its patch if there is one, and records what it wrote. It does not overwrite a file of TREE that was edited since
and not saved, unless `--force` is given. `save` writes, for every file of TREE that differs from the library's,
the difference as a patch, and removes the patch of a file that no longer differs. The work on a port is: `make`,
edit the files of TREE and compile them (`bundle_files.py`), `save`. `errors` prints what the last compile
recorded for a module, with the lines around each error.
"""
import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ROOTS = ["lib/core", "lib/pnt", "lib/dh", "lib/zeta23", "lib/vendor/pnt-plus", "lib/vendor/zeta23"]
IMPORT = re.compile(r"^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(.*)$")
RECORD = ".port.json"


def header(text):
    """The modules a file imports. Comments may come before and between the imports."""
    imports, depth = [], 0
    for line in text.split("\n"):
        s = line.strip()
        if depth:  # inside a block comment
            depth += s.count("/-") - s.count("-/")
            continue
        if s.startswith("/-"):
            depth = s.count("/-") - s.count("-/")
            continue
        m = IMPORT.match(line)
        if m:
            imports.extend(m.group(1).split("--")[0].split())
            continue
        if s == "" or s == "module" or s.startswith("--"):
            continue
        break
    return imports


def sha(text):
    return hashlib.sha1(text.encode()).hexdigest()


def read(p):
    with open(p, encoding="utf-8") as f:
        return f.read()


def library():
    """Module name -> path from the repository's root."""
    where = {}
    for root in ROOTS:
        top = os.path.join(REPO, root)
        for d, dirs, files in os.walk(top):
            dirs.sort()
            for name in sorted(files):
                if name.endswith(".lean"):
                    p = os.path.join(d, name)
                    where.setdefault(os.path.relpath(p, top)[:-5].replace(os.sep, "."), os.path.relpath(p, REPO))
    return where


def reach(target, where):
    name = os.path.basename(target)[:-5]
    where = dict(where)
    where[name] = os.path.relpath(os.path.abspath(target), REPO)
    seen, stack = {}, [name]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen[m] = where[m]
        for i in header(read(os.path.join(REPO, where[m]))):
            if i in where:
                stack.append(i)
    return seen


def patch_path(patches, module):
    return os.path.join(patches, module + ".patch")


def tree_path(tree, module):
    return os.path.join(tree, *module.split(".")) + ".lean"


def patched(original_path, patch):
    """The text of a file of the library with a patch applied."""
    r = subprocess.run(["/usr/bin/patch", "--quiet", "-o", "-", original_path, patch], capture_output=True)
    if r.returncode != 0:
        raise SystemExit("the patch %s does not apply to %s:\n%s" % (patch, original_path,
                                                                     (r.stdout + r.stderr).decode()[-800:]))
    return r.stdout.decode()


def load_record(tree):
    p = os.path.join(tree, RECORD)
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return {}


def make(args):
    tree, patches = os.path.abspath(args.tree), os.path.abspath(args.patches)
    mods = reach(args.target, library())
    record = load_record(tree)
    kept, wrote, with_patch = 0, 0, 0
    for m in sorted(mods):
        src = os.path.join(REPO, mods[m])
        original = read(src)
        pp = patch_path(patches, m)
        text = patched(src, pp) if os.path.exists(pp) else original
        with_patch += os.path.exists(pp)
        out = tree_path(tree, m)
        if os.path.exists(out):
            now = read(out)
            if now == text:
                record[m] = dict(source=mods[m], original=sha(original), written=sha(text))
                kept += 1
                continue
            if record.get(m, {}).get("written") != sha(now) and not args.force:
                raise SystemExit("%s was edited and not saved (`save`, or `make --force` to lose the edits)" % out)
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, "w", encoding="utf-8") as f:
            f.write(text)
        record[m] = dict(source=mods[m], original=sha(original), written=sha(text))
        wrote += 1
    for m in sorted(set(record) - set(mods)):
        out = tree_path(tree, m)
        if os.path.exists(out):
            os.remove(out)
        del record[m]
    with open(os.path.join(tree, RECORD), "w") as f:
        json.dump(record, f, indent=1, sort_keys=True)
    print("%d modules: %d written, %d as they were; %d with a patch" % (len(mods), wrote, kept, with_patch))


def differing(tree, record):
    for m in sorted(record):
        src = os.path.join(REPO, record[m]["source"])
        original, now = read(src), read(tree_path(tree, m))
        if sha(original) != record[m]["original"]:
            raise SystemExit("%s changed in the library since `make`: run `make` again first" % record[m]["source"])
        yield m, src, original, now


def save(args):
    tree, patches = os.path.abspath(args.tree), os.path.abspath(args.patches)
    record = load_record(tree)
    os.makedirs(patches, exist_ok=True)
    n = 0
    for m, src, original, now in differing(tree, record):
        pp = patch_path(patches, m)
        if now == original:
            if os.path.exists(pp):
                os.remove(pp)
        else:
            rel = record[m]["source"]
            r = subprocess.run(["/usr/bin/diff", "-u", "--label", "a/" + rel, "--label", "b/" + rel, src,
                                tree_path(tree, m)], capture_output=True)
            if r.returncode not in (0, 1):
                raise SystemExit(r.stderr.decode())
            with open(pp, "wb") as f:
                f.write(r.stdout)
            n += 1
        record[m]["written"] = sha(now)
    with open(os.path.join(tree, RECORD), "w") as f:
        json.dump(record, f, indent=1, sort_keys=True)
    print("%d patches in %s" % (n, os.path.relpath(patches, REPO)))


DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |nonrec |unsafe |partial )*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|example)\b")


def status(args):
    """The changed lines, and those that may touch a statement: a changed line from the start of a declaration to
    the `:=` or `where` that ends its statement."""
    tree = os.path.abspath(args.tree)
    record = load_record(tree)
    files = lines = 0
    for m, src, original, now in differing(tree, record):
        if now == original:
            continue
        files += 1
        a, b = original.split("\n"), now.split("\n")
        suspicious = []
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
            if tag == "equal":
                continue
            lines += max(i2 - i1, j2 - j1)
            for k in range(i1, max(i2, i1 + 1)):
                # walk back to the start of the declaration and see whether the statement has ended before line k
                s = k
                while s > 0 and not DECL.match(a[s]):
                    s -= 1
                head = "\n".join(a[s:k])
                if DECL.match(a[s]) and not re.search(r":=|\bwhere\b|^\s*\|", head, re.M):
                    suspicious.append(k + 1)
        if suspicious or args.verbose:
            print("%-40s statement lines touched: %s" % (m, suspicious if suspicious else "none"))
    print("%d files differ from the library, about %d lines" % (files, lines))


def errors(args):
    """The errors that `bundle_files.py` recorded for some modules (all, if none is named), each with the lines of
    the file around it."""
    tree = os.path.abspath(args.tree)
    with open(os.path.join(os.path.abspath(args.build), "state.json")) as f:
        state = json.load(f)
    for m in (args.modules or sorted(m for m in state if state[m]["errors"])):
        rows = state.get(m, {}).get("errors", [])
        if not args.modules:
            print("%-44s %d" % (m, len(rows)))
            continue
        p = tree_path(tree, m)
        text = read(p).split("\n") if os.path.exists(p) else []
        print("== %s: %d errors" % (m, len(rows)))
        for line, col, msg in rows:
            print("-- %s:%d:%d" % (m, line, col))
            for k in range(max(0, line - 1 - args.context), min(len(text), line + args.context)):
                print("%s%5d  %s" % (">" if k == line - 1 else " ", k + 1, text[k]))
            print("   " + msg[:args.chars].replace("\n", "\n   "))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("command", choices=["make", "save", "status", "errors"])
    ap.add_argument("tree")
    ap.add_argument("--target", default=os.path.join(REPO, "scratch/rh-claim/RHClaim.lean"))
    ap.add_argument("--patches", default=os.path.join(REPO, "scratch/rh-claim/port/patches"))
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--build", default=os.path.join(REPO, "external/alpoge-rh/port/build"),
                    help="the output of bundle_files.py, for `errors`")
    ap.add_argument("--context", type=int, default=3)
    ap.add_argument("--chars", type=int, default=1500)
    ap.add_argument("modules", nargs="*")
    args = ap.parse_args()
    {"make": make, "save": save, "status": status, "errors": errors}[args.command](args)


if __name__ == "__main__":
    main()
