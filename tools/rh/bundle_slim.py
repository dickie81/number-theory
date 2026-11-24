#!/usr/bin/env python3
"""Keep, beside each compiled bundle, the copy without the proofs of theorems that the bundles above import.

    python3 -I tools/rh/bundle_slim.py --out OUT [--jobs 3] [--workspace WS]

To import a module Lean looks at every constant in it, and in a compiled file the constants lie among their
proofs, so an import reads every page of every bundle below: 30 GB at the 34th level of the archive, more than
five processes leave free in 32 GB, and so mostly from the disk, for each bundle again. An import took three
minutes there, more than compiling the bundle, and would have taken longer with every level.

`lean/Slim.lean` writes OUT/olean-slim/B/<name>.olean: the same constants with their types, the definitions with
their values, and for the value of each theorem a constant that does not exist. It is a fifth of the size.
`bundle_build.py` and `bundle_recheck.py` put that directory before OUT/olean on the path, so a bundle is compiled
and checked against the slim copies of what is below it, and written whole; `bundle_check.py`, which reads what a
theorem rests on, uses the whole files. `lean/Slim.lean` says why nothing is lost by it.

This script makes the copies that are missing or older than their bundle; `bundle_build.py` does the same when it
starts and after each level.

The kernel does need a proof sometimes (a function defined by well-founded recursion that it computes: it
unfolds the proof that the recursion ends; a proof by recursion that it is made to run). The copy has `_slim_.T`
for the proof of `T`, the kernel's message names it, and `bundle_build.py` and `bundle_recheck.py` put `T` in
OUT/slim-keep.json, make the copy of its bundle again with the proof left in, and try once more. The proof of
`T` is as a rule another theorem applied to proofs, which the kernel unfolds next: `bundle_build.py` follows
that chain at once, from the heads of the kept proofs that `lean/Slim.lean` names (`make`, `heads`).
"""
import argparse
import importlib.util
import json
import os
import subprocess
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def stale(out):
    """The bundles on record whose slim copy is missing or older than the bundle."""
    last = {}
    with open(os.path.join(out, "state.jsonl")) as f:
        for line in f:
            r = json.loads(line)
            last[r["bundle"]] = r
    todo = []
    for b in sorted(last):
        full = os.path.join(out, "olean", "B", b + ".olean")
        slim = os.path.join(out, "olean-slim", "B", b + ".olean")
        if not last[b]["ok"] or not os.path.exists(full):
            continue
        if not os.path.exists(slim) or os.stat(slim).st_mtime_ns < os.stat(full).st_mtime_ns:
            todo.append(b)
    return todo


def kept(out):
    """The theorems whose proofs the copies keep: those that a kernel check of a bundle above needed."""
    path = os.path.join(out, "slim-keep.json")
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return []


def keep_more(out, names):
    """Put theorems on that list; returns the ones that were not on it."""
    have = kept(out)
    new = [n for n in names if n not in have]
    if new:
        with open(os.path.join(out, "slim-keep.json"), "w") as f:
            json.dump(sorted(have + new), f, ensure_ascii=False, indent=0)
    return new


def make(out, lean, prefix, env, names, jobs=1, heads=None):
    """Write the slim copies of the named bundles, in `jobs` processes. Returns (copies made, bytes, bytes of
    the whole files). `heads`, a dict, is filled with what `lean/Slim.lean` says of each theorem whose proof a
    copy keeps: the constants at the head of that proof, which the kernel may unfold next."""
    os.makedirs(os.path.join(out, "olean-slim", "B"), exist_ok=True)
    keep = kept(out)
    procs = []
    for k in range(jobs):
        part = names[k::jobs]
        if not part:
            continue
        path = os.path.join(out, "olean-slim", "job%d.json" % k)
        with open(path, "w") as f:
            json.dump(dict(files=[[os.path.join(out, "olean", "B", b + ".olean"),
                                   os.path.join(out, "olean-slim", "B", b + ".olean"), "B." + b] for b in part],
                           keep=keep), f, ensure_ascii=False)
        procs.append((part, subprocess.Popen(prefix + [lean, "--run", os.path.join(HERE, "lean", "Slim.lean"), path],
                                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)))
    made = small = whole = 0
    for part, p in procs:
        text = p.communicate()[0]
        for line in text.split("\n"):
            if line.startswith('{"slim"'):
                r = json.loads(line)
                made += 1
                small += r["bytes"]
                whole += r["of"]
                if heads is not None:
                    heads.update(r.get("heads", {}))
        if p.returncode != 0:
            raise SystemExit("Slim.lean failed on one of %s …: %s" % (" ".join(part[:3]), text[-600:]))
    return made, small, whole


def ensure(out, ws, jobs=3, say=True, every=False):
    """Make the copies that are missing or out of date. Lean takes a module from the first directory of its path
    that holds the package, and does not look further: with the copies first on the path, a bundle without a
    copy is a bundle that is not there."""
    bb = load("bundle_build")
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    os.makedirs(os.path.join(out, "olean-slim", "B"), exist_ok=True)
    profile = os.path.join(out, "olean-slim", "sandbox.sb")
    with open(profile, "w") as f:
        f.write(bb.sandbox_profile(os.path.join(out, "olean-slim"),
                                   [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), out, HERE]))
    todo = stale(out)
    if every:
        last = {}
        with open(os.path.join(out, "state.jsonl")) as f:
            for line in f:
                r = json.loads(line)
                last[r["bundle"]] = r
        todo = [b for b in sorted(last) if last[b]["ok"] and os.path.exists(os.path.join(out, "olean", "B", b + ".olean"))]
    if say:
        print("%d bundles to copy without their proofs" % len(todo), flush=True)
    if not todo:
        return 0
    t0 = time.time()
    made, small, whole = make(out, lean, ["/usr/bin/sandbox-exec", "-f", profile], dict(os.environ), todo, jobs)
    if say:
        print("%d copies in %.0f s: %.1f GB for %.1f GB" % (made, time.time() - t0, small / 1e9, whole / 1e9),
              flush=True)
    return made


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--workspace", default=os.path.join(ext, "native-ws"))
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--all", action="store_true", help="make every copy again (after a change to lean/Slim.lean)")
    args = ap.parse_args()
    ensure(os.path.abspath(args.out), os.path.abspath(args.workspace), args.jobs, every=args.all)


if __name__ == "__main__":
    main()
