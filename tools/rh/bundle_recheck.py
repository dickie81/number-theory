#!/usr/bin/env python3
"""Check every bundle of a build again in the kernel, against the bundles below it as they are now.

    python3 -I tools/rh/bundle_recheck.py --out OUT [--jobs 5] [--bundle NAME ...] [--workspace WS]

`bundle_build.py` compiles a bundle again after a repair and leaves the bundles above it as they are: their
proofs were checked against the statements that the bundle held before the repair. For a proof that failed and
was mended that is sound. It is not if the repair changed a statement, and a repair of a name read as the wrong
constant can. This script closes the gap without compiling anything again: for each bundle, `lean/Recheck.lean`
imports what the bundle imports, as it is now, and sends every constant of the bundle's `.olean` to the kernel
once more. A bundle that passes is a correct extension of what is below it now; when every bundle passes, the
whole build is, whatever the order in which its parts were made.

What a bundle imports is read from the copies without proofs that `bundle_slim.py` keeps (an import of the
whole files reads tens of gigabytes): a check that passes against them passes against the whole files, because
it never looked at a proof, and one that needs a proof is refused with `_slim_` in the message and is then
checked again against the whole files (`--full` does that for every bundle). The bundle itself is read whole, so
every proof is checked, in its own bundle.

OUT/recheck.jsonl has a line a bundle: its name, whether the kernel accepted it, the number of constants, and a
signature of the `.olean` files involved (the bundle's and those of the bundles it imports). A bundle is checked
again only when that signature has changed, so the script can be run after each repair; the result is final when
it reports no bundle to check and none refused.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--workspace", default=os.path.join(ext, "native-ws"))
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--jobs", type=int, default=5)
    ap.add_argument("--bundle", nargs="*", default=[], help="these bundles only")
    ap.add_argument("--max-level", type=int, default=0)
    ap.add_argument("--full", action="store_true",
                    help="import the whole files of the bundles below for every bundle, not only for one that the "
                         "kernel refuses for want of a proof")
    args = ap.parse_args()
    bb = load("bundle_build")
    out = os.path.abspath(args.out)
    os.makedirs(os.path.join(out, "recheck"), exist_ok=True)
    last = {}
    with open(os.path.join(out, "state.jsonl")) as f:
        for line in f:
            r = json.loads(line)
            last[r["bundle"]] = r
    names = [b for b in sorted(last) if last[b]["ok"] and last[b]["files"]]
    if args.bundle:
        names = [b for b in names if b in set(args.bundle)]
    if args.max_level:
        names = [b for b in names if last[b]["level"] <= args.max_level]
    olean = {b: os.path.join(out, "olean", "B", b + ".olean") for b in last}
    stamp = {}

    def sig(b, imports):
        h = hashlib.sha1()
        for x in [b] + sorted(i[2:] for i in imports if i.startswith("B.")):
            if x not in stamp:
                try:
                    st = os.stat(olean[x])
                    stamp[x] = "%d:%d" % (st.st_mtime_ns, st.st_size)
                except (OSError, KeyError):
                    stamp[x] = "-"
            h.update((x + "=" + stamp[x] + ";").encode())
        return h.hexdigest()

    record_path = os.path.join(out, "recheck.jsonl")
    seen = {}
    if os.path.exists(record_path):
        with open(record_path) as f:
            for line in f:
                r = json.loads(line)
                seen[r["bundle"]] = r
    todo = []
    below = defaultdict(list)       # level -> the bundles of the levels below it, as they are now
    for b in names:
        with open(os.path.join(out, "job", b + ".json")) as f:
            imports = json.load(f)["imports"]
        if not last[b].get("exact"):
            # every bundle of a lower level that the build holds now, not the ones that were there when the
            # bundle was compiled: a file compiled again in a bundle of its own has left the one it was in
            lv = last[b]["level"]
            if lv not in below:
                below[lv] = ["B." + x for x in sorted(last) if last[x]["ok"] and last[x]["level"] < lv]
            imports = [i for i in imports if not i.startswith("B.")] + below[lv]
        s = sig(b, imports)
        if seen.get(b, {}).get("sig") == s and seen[b]["ok"]:
            continue
        todo.append((b, imports, s))
    print("%d bundles; %d to check" % (len(names), len(todo)), flush=True)
    ws = os.path.abspath(args.workspace)
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True, text=True,
                               check=True).stdout.strip()
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    # what the bundle imports is read from the copies without proofs (`bundle_slim.py`): the kernel needs the
    # statements of the theorems below, and a check that would need a proof stops at `_slim_` and is refused.
    # The bundle under check is read from its whole file
    paths = ([] if args.full else [os.path.join(out, "olean-slim")]) + [os.path.join(out, "olean")]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths + [lean_path]))
    if not args.full:
        # with the copies first on the path a bundle without a copy is not found at all: they are made first
        made = load("bundle_slim").ensure(out, ws, min(3, args.jobs), say=False)
        if made:
            print("%d copies without proofs made" % made, flush=True)
    profile = os.path.join(out, "recheck", "sandbox.sb")
    with open(profile, "w") as f:
        f.write(bb.sandbox_profile(os.path.join(out, "recheck"),
                                   [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), out, HERE]))
    env_whole = dict(os.environ, LEAN_PATH=os.pathsep.join(paths[-1:] + [lean_path]))
    slim = load("bundle_slim")
    slim_profile = os.path.join(out, "olean-slim", "sandbox.sb")
    tries, table = {}, {}

    def holders_of(theorems):
        """The bundles that hold these theorems (`bundle_build.py`, `holders`), from the map and the record."""
        if not table:
            import pickle
            with open(os.path.join(args.map, "graph.pkl"), "rb") as f:
                g = pickle.load(f)
            table.update(arch=g["arch"], d_file=g["d_file"],
                         file_of={rel[:-5].replace(os.sep, "."): i for i, rel in enumerate(g["files"])},
                         where={f: b for b in last if last[b]["ok"] for f in last[b]["files"]})
        found = set()
        for name in theorems:
            parts, f = name.split("."), None
            if parts[0] == "_private" and "0" in parts:
                f = table["file_of"].get(".".join(parts[1:parts.index("0")]))
            k = len(parts)
            while f is None and k > 0:
                d = table["arch"].get(".".join(parts[:k]))
                if d is not None:
                    f = table["d_file"][d]
                k -= 1
            if f is None or f not in table["where"]:
                return None
            found.add(table["where"][f])
        return sorted(found)
    running, refused, t0, n = {}, [], time.time(), 0
    whole = set()       # refused for want of a proof: checked again against the whole files
    queue = list(todo)
    while queue or running:
        while queue and len(running) < args.jobs:
            b, imports, s = queue.pop(0)
            jp = os.path.join(out, "recheck", b + ".json")
            with open(jp, "w") as f:
                json.dump(dict(imports=imports, olean=olean[b]), f)
            cmd = ["/usr/bin/sandbox-exec", "-f", profile, lean, "--tstack=400000", "--run",
                   os.path.join(HERE, "lean", "Recheck.lean"), jp]
            running[b] = (subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                           env=env_whole if b in whole else env), s, imports)
        done = [b for b, v in running.items() if v[0].poll() is not None]
        if not done:
            time.sleep(0.2)
            continue
        for b in done:
            p, s, imports = running.pop(b)
            text = p.stdout.read()
            r = None
            for line in text.split("\n"):
                if line.startswith("{"):
                    try:
                        r = json.loads(line)
                    except ValueError:
                        pass
            if r is None:
                r = dict(ok=False, error="the process gave no answer: " + text[-500:])
            if not r["ok"] and "_slim_" in r.get("error", "") and b not in whole and not args.full:
                # the kernel names the proof it needed: it is kept in the copy of its bundle, which is made
                # again, and the check is run once more; failing that, against the whole files
                wanted = sorted(set(bb.SLIM_NAME.findall(r["error"])))
                holders = holders_of(wanted) if wanted and tries.get(b, 0) < 6 else None
                if holders and slim.keep_more(out, wanted):
                    slim.make(out, lean, ["/usr/bin/sandbox-exec", "-f", slim_profile], dict(os.environ), holders, 1)
                    tries[b] = tries.get(b, 0) + 1
                    print("   %s: the kernel needed the proof of %s; kept in the copy of %s, and checked again"
                          % (b, ", ".join(wanted)[:200], " ".join(holders)), flush=True)
                else:
                    whole.add(b)
                    print("   %s: the kernel needed a proof of a bundle below; checked again against the whole "
                          "files" % b, flush=True)
                queue.append((b, imports, s))
                continue
            r.update(bundle=b, sig=s, whole=b in whole or args.full)
            with open(record_path, "a") as f:
                f.write(json.dumps(r, ensure_ascii=False) + "\n")
            n += 1
            if not r["ok"]:
                refused.append(b)
                print("   REFUSED %s: %s" % (b, r.get("error", "")[:600]), flush=True)
            if n % 50 == 0:
                print("%d checked, %d refused, %.0f s" % (n, len(refused), time.time() - t0), flush=True)
    print("%d checked in %.0f s; refused: %s" % (n, time.time() - t0, " ".join(refused) or "none"))


if __name__ == "__main__":
    main()
