#!/usr/bin/env python3
"""The Lake targets that validate a change, one per line, for CI's Lean build.

    python3 scripts/lean_targets.py BASE   # for the changes from the commit BASE to HEAD
    python3 scripts/lean_targets.py --all  # every library of the lakefile

A change to a module is validated by building the module and every module that imports it, directly or not; Lake
builds their own imports. So the targets are `Check` (the papers' theorems), `CheckAll` (every final theorem of the
library) and `CheckZeta23` (those of the zeta23 layer, which `CheckAll` cannot import), always, and, as `+Module`:
- every module of `lib/` that the change adds or edits, the vendored libraries' included;
- every module that imports one of these, or a module that the change deletes or renames;
- every library that the change adds to `lakefile.lean`.
They are every library of the lakefile instead when `lean-toolchain` or `lake-manifest.json` changes, or
`lakefile.lean` changes outside its module lists in another way than by adding a library, since such a change can
reach every module.

The import graph is read from the working tree, which should be at HEAD, as `import_cone.py` reads it, with the
vendored libraries' modules under their hierarchical names.
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_cone  # noqa: E402

ROOT = import_cone.ROOT
WHOLE = {"lean-toolchain", "lake-manifest.json"}
ALWAYS = ["Check", "CheckAll", "CheckZeta23"]


def graph():
    """The modules of `lib/`, each with the names its `import` lines give."""
    mods, _ = import_cone.sources()
    vendor = os.path.join("lib", "vendor")
    for lib in sorted(os.listdir(os.path.join(ROOT, vendor))):
        for d, _, files in os.walk(os.path.join(ROOT, vendor, lib)):
            for f in files:
                if f.endswith(".lean"):
                    p = os.path.relpath(os.path.join(d, f), ROOT)
                    mods[os.path.relpath(p, os.path.join(vendor, lib))[:-5].replace(os.sep, ".")] = p
    imports = {m: re.findall(r"^import\s+(\S+)", open(os.path.join(ROOT, p), encoding="utf-8").read(), re.M)
               for m, p in mods.items()}
    return mods, imports


def module_of(path):
    """The module that a path of the repository holds, or None."""
    parts = path.split("/")
    if not path.endswith(".lean") or len(parts) < 3 or parts[0] != "lib":
        return None
    if parts[1] == "vendor":
        return ".".join(parts[3:])[:-5] if len(parts) > 3 else None
    return parts[2][:-5] if parts[1] in import_cone.DIRS and len(parts) == 3 else None


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def lakefile_settings(rev):
    """`lakefile.lean` at `rev` without its module lists, which `gen_lakefile.py` writes as `.one` rows under a
    `/-- lib/<layer>: <n> modules. -/` line, and without blank lines: its preamble, under the key None, and each
    library's lines, from the docstring and attributes above its `lean_lib` line, under the library's name."""
    try:
        text = git("show", f"{rev}:lakefile.lean")
    except subprocess.CalledProcessError:
        return None
    blocks, name, above = {None: []}, None, []
    for line in text.splitlines():
        if (not line.strip() or line.lstrip().startswith(".one ")
                or re.fullmatch(r"/-- lib/\w+: \d+ modules\. -/", line)):
            continue
        m = re.match(r"lean_lib\s+(\S+)\s+where", line)
        if m:
            name = m.group(1)
            blocks[name], above = above + [line], []
        elif line.startswith(("/--", "@[")):
            above.append(line)
        else:
            blocks[name] += above + [line]
            above = []
    blocks[name] += above
    return blocks


def libraries():
    text = open(os.path.join(ROOT, "lakefile.lean"), encoding="utf-8").read()
    return re.findall(r"^lean_lib\s+(\S+)\s+where", text, re.M)


def targets(base):
    changed, added, whole = set(), set(), False
    for line in git("diff", "--name-status", "--no-renames", base, "HEAD").splitlines():
        path = line.split("\t", 1)[1]
        if path in WHOLE:
            whole = True
        elif path == "lakefile.lean":
            old, new = lakefile_settings(base), lakefile_settings("HEAD")
            if old is None or new is None or any(new.get(k) != v for k, v in old.items()):
                whole = True
            else:
                added = set(new) - set(old)
        elif module_of(path):
            changed.add(module_of(path))
    if whole:
        return libraries()
    mods, imports = graph()
    importers = {}
    for m, names in imports.items():
        for n in names:
            importers.setdefault(n, set()).add(m)
    reached, stack = set(changed), list(changed)
    while stack:
        for m in importers.get(stack.pop(), ()):
            if m not in reached:
                reached.add(m)
                stack.append(m)
    return ALWAYS + sorted(added - set(ALWAYS)) + sorted("+" + m for m in reached if m in mods and m not in ALWAYS)


def main(argv):
    if argv == ["--all"]:
        print("\n".join(libraries()))
    elif len(argv) == 1 and not argv[0].startswith("-"):
        print("\n".join(targets(argv[0])))
    else:
        print("\n".join(line.strip() for line in __doc__.splitlines()[2:4]), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
