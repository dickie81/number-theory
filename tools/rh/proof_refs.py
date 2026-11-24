#!/usr/bin/env python3
"""After bundles were compiled again: the bundles above them whose terms name a constant that is not the same.

    python3 -I tools/rh/proof_refs.py --out OUT BUNDLE [BUNDLE ...] [--workspace WS]

A bundle that is compiled again replaces its compiled file, and the bundles above it were checked by the kernel
against the earlier one. `bundle_recheck.py` finds every bundle that no longer fits, at the price of a kernel
check of the whole build; this script names the few to check now, in a few minutes, by reading the compiled
files as data (`lean/ProofRefs.lean`).

It reads the bundles above the given ones that were last compiled before one of them was (a bundle compiled
since was checked against what is there now), and prints those that name a constant of the given bundles which
is gone, which has another type or value than it had (`changed`: exact, from the `<name>.olean.before` that
`bundle_build.py` keeps), or, for a bundle without that file, a lifted proof `d._proof_2` which may have been
numbered otherwise (`moved`: `lean/ProofRefs.lean` tells how they are found). It ends with the
`bundle_recheck.py` command for those bundles. When the kernel accepts all of them, delete the `.before` files
of the given bundles (`--settled`): the next comparison is then against what they hold now.
"""
import argparse
import importlib.util
import json
import os
import subprocess

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
    ap.add_argument("--settled", action="store_true", help="delete the .olean.before of the given bundles, and stop")
    ap.add_argument("bundle", nargs="+")
    args = ap.parse_args()
    bb = load("bundle_build")
    out = os.path.abspath(args.out)
    last, at = {}, {}
    with open(os.path.join(out, "state.jsonl")) as f:
        for k, line in enumerate(f):
            r = json.loads(line)
            last[r["bundle"]] = r
            at[r["bundle"]] = k
    watch = set(args.bundle)
    missing = [b for b in watch if b not in last]
    if missing:
        raise SystemExit("not bundles of the build: " + " ".join(missing))
    floor = min(last[b]["level"] for b in watch)
    newest = max(at[b] for b in watch)
    scan = [b for b in sorted(last) if b not in watch and last[b]["ok"] and last[b]["files"]
            and last[b]["level"] > floor and at[b] < newest]
    olean = lambda b: os.path.join(out, "olean", "B", b + ".olean")
    before = {b: olean(b) + ".before" for b in watch if os.path.exists(olean(b) + ".before")}
    if args.settled:
        for b in sorted(before):
            os.remove(before[b])
        print("%d earlier files deleted" % len(before))
        return
    work = os.path.join(out, "recheck")
    os.makedirs(work, exist_ok=True)
    job = os.path.join(work, "proof-refs.json")
    with open(job, "w") as f:
        # (the bundles of the same levels made since: a file that failed in its bundle and was compiled again
        # in one of its own has taken its declarations there)
        levels = {last[b]["level"] for b in watch}
        moved_to = [b for b in sorted(last) if b not in watch and last[b]["ok"] and last[b]["files"]
                    and last[b]["level"] in levels and os.path.exists(olean(b))]
        json.dump(dict(watch=[olean(b) for b in sorted(watch)], before=[before.get(b, "") for b in sorted(watch)],
                       scan=[olean(b) for b in scan], elsewhere=[olean(b) for b in moved_to]), f)
    ws = os.path.abspath(args.workspace)
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    profile = os.path.join(work, "sandbox.sb")
    with open(profile, "w") as f:
        f.write(bb.sandbox_profile(work, [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), out, HERE]))
    p = subprocess.run(["/usr/bin/sandbox-exec", "-f", profile, lean, "--run",
                        os.path.join(HERE, "lean", "ProofRefs.lean"), job], capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit("ProofRefs.lean failed: " + (p.stderr or p.stdout)[-800:])
    found = []
    for line in p.stdout.split("\n"):
        if not line.startswith("{"):
            continue
        r = json.loads(line)
        if "olean" not in r:
            print("%d of the given bundles are compared with what they held before, %d by their lifted proofs alone; "
                  "of their constants %d are gone, %d have changed, %d lifted proofs may have another number"
                  % (len(before), len(watch) - len(before), r["gone"], r["changed"], r["moved"]))
            continue
        b = os.path.basename(r["olean"])[:-len(".olean")]
        found.append(b)
        print("%s  gone %d  changed %d  moved %d  %s" % (b, len(r["gone"]), len(r["changed"]), len(r["moved"]),
                                                       " ".join((r["gone"] + r["changed"] + r["moved"])[:4])))
    print("%d bundles above %s read; %d name a constant that is gone, has changed or may have moved"
          % (len(scan), " ".join(sorted(watch)), len(found)))
    if found:
        print("python3 -I tools/rh/bundle_recheck.py --out %s --jobs 1 --bundle %s" % (args.out, " ".join(found)))


if __name__ == "__main__":
    main()
