#!/usr/bin/env python3
"""Check every declaration of a bundled build again in the kernel, in one pass over the whole files.

    python3 -I tools/rh/bundle_replay.py --out OUT [--threads 8] [--max-level N] [--fresh] [--rehash]

`bundle_recheck.py` checks a bundle against what is below it by importing all of it, a process a bundle: right
for the few bundles above a repair, hours for a whole build, most of them spent importing. This is the check of
the whole build. `lean/ReplayAll.lean` starts from the modules that the archive imports from outside (Mathlib)
and goes through the bundles in the order of their levels. It reads each `.olean` as data, puts every constant
in the environment, and has the kernel check each one, on all the threads, against the environment as it was
just before that constant: Mathlib and the constants before it, with their proofs. Nothing of the build is
imported, so no copy without proofs is read (`bundle_slim.py`), and the order in which the bundles were made,
compiled again and repaired plays no part. If every check passes, every constant of the build is a declaration
that the kernel accepts over Mathlib and the constants before it; `lean/ReplayAll.lean` gives the argument.

The pass also reports what `bundle_axioms.py` looks for: the constants that a bundle declares as axioms, and the
axioms below the build that its constants name (`sorryAx` is one: a declaration whose elaboration failed).

OUT/replay.jsonl has a line for every bundle that a pass accepted or refused, with the SHA-1 of its `.olean`
and of the chain up to it (the outside modules, then every bundle before it, by name and bytes). A later pass
does not check again the bundles at the start of the order whose chain it finds accepted there: they are put in
the environment and nothing is sent to the kernel for them. From the first bundle that is new, or changed, or
comes after one that is, everything is checked. So a pass that was interrupted is taken up where it stopped,
and after a repair the pass checks the repaired bundle and all that comes after it. `--fresh` checks
everything. The result is final when a pass ends with nothing refused and no file changed under it.

A single check can need gigabytes (a proof that the kernel computes), whatever the number of threads; with
eight threads the pass has stayed inside 32 GB.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
STANDARD = ("propext", "Classical.choice", "Quot.sound")


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sha1_of(path):
    h = hashlib.sha1()
    with open(path, "rb") as f:
        while True:
            block = f.read(1 << 22)
            if not block:
                return h.hexdigest()
            h.update(block)


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--workspace", default=os.path.join(ext, "native-ws"))
    ap.add_argument("--scan", default=os.path.join(ext, "scan.json"))
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--window", type=int, default=4000, help="checks that wait at most, before the pass reads on")
    ap.add_argument("--max-level", type=int, default=0, help="stop after the bundles of this level")
    ap.add_argument("--fresh", action="store_true", help="check every bundle, whatever an earlier pass accepted")
    ap.add_argument("--rehash", action="store_true",
                    help="read every file for its SHA-1, also those whose size and time are as they were")
    ap.add_argument("--nice", type=int, default=0, help="run the pass at this niceness (beside a build)")
    args = ap.parse_args()
    out = os.path.abspath(args.out)
    work = os.path.join(out, "replay")
    os.makedirs(work, exist_ok=True)
    last = {}
    with open(os.path.join(out, "state.jsonl")) as f:
        for line in f:
            r = json.loads(line)
            last[r["bundle"]] = r
    names = [b for b in sorted(last, key=lambda b: (last[b]["level"], b)) if last[b]["ok"] and last[b]["files"]]
    if args.max_level:
        names = [b for b in names if last[b]["level"] <= args.max_level]
    olean = {b: os.path.join(out, "olean", "B", b + ".olean") for b in names}
    gone = [b for b in names if not os.path.exists(olean[b])]
    if gone:
        raise SystemExit("on record and not there: %s" % " ".join(gone[:20]))
    failing = sum(len(last[b]["errors"]) for b in names)

    # the SHA-1 of each file; a file whose size and time are those of the last time is not read again
    cache_path = os.path.join(work, "sha1.json")
    cache = {}
    if os.path.exists(cache_path) and not args.rehash:
        with open(cache_path) as f:
            cache = json.load(f)

    def stamp(b):
        st = os.stat(olean[b])
        return "%d:%d" % (st.st_size, st.st_mtime_ns)

    stamps = {b: stamp(b) for b in names}
    todo = [b for b in names if cache.get(b, [None])[0] != stamps[b]]
    t0 = time.time()
    with ThreadPoolExecutor(4) as pool:
        for b, digest in zip(todo, pool.map(lambda b: sha1_of(olean[b]), todo)):
            cache[b] = [stamps[b], digest]
    if todo:
        with open(cache_path + ".part", "w") as f:
            json.dump({b: cache[b] for b in names}, f)
        os.replace(cache_path + ".part", cache_path)
        print("%d files read for their SHA-1 in %.0f s" % (len(todo), time.time() - t0), flush=True)
    sig = {b: cache[b][1] for b in names}

    # the modules from outside the archive, as `bundle_build.py` gives them to every bundle
    with open(args.scan) as f:
        external = json.load(f)["external"]
    imports = sorted(x for x in external if not x.startswith("Mathlib.")) if "Mathlib" in external else sorted(external)
    ws = os.path.abspath(args.workspace)
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True, text=True,
                               check=True).stdout.strip()
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    version = subprocess.run([lean, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    with open(os.path.join(ws, "lake-manifest.json"), "rb") as f:
        manifest = hashlib.sha1(f.read()).hexdigest()
    h = hashlib.sha1(("%s;%s;%s;" % (version, manifest, " ".join(imports))).encode())
    chain = {}
    for b in names:
        h.update(("%s=%s;" % (b, sig[b])).encode())
        chain[b] = h.hexdigest()

    record_path = os.path.join(out, "replay.jsonl")
    accepted = set()
    if os.path.exists(record_path) and not args.fresh:
        with open(record_path) as f:
            for line in f:
                r = json.loads(line)
                if r.get("ok"):
                    accepted.add(r["chain"])
    trusted = 0
    while trusted < len(names) and chain[names[trusted]] in accepted:
        trusted += 1
    print("%d bundles on %d levels, %d declarations that the build left with an error; %d accepted by an earlier "
          "pass and unchanged, %d to check" % (len(names), len({last[b]["level"] for b in names}), failing, trusted,
                                               len(names) - trusted), flush=True)
    if trusted == len(names):
        print("nothing to check")
    job = os.path.join(work, "job.json")
    with open(job, "w") as f:
        json.dump(dict(imports=imports, window=args.window,
                       bundles=[[b, olean[b], "trust" if k < trusted else "check"] for k, b in enumerate(names)]), f)
    bb = load("bundle_build")
    profile = os.path.join(work, "sandbox.sb")
    with open(profile, "w") as f:
        f.write(bb.sandbox_profile(work, [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), out, HERE]))
    cmd = ["/usr/bin/sandbox-exec", "-f", profile, lean, "-j", str(args.threads), "--tstack=400000", "--run",
           os.path.join(HERE, "lean", "ReplayAll.lean"), job]
    if args.nice:
        cmd = ["/usr/bin/nice", "-n", str(args.nice)] + cmd
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            env=dict(os.environ, LEAN_PATH=lean_path))
    pass_id = time.strftime("%Y-%m-%dT%H:%M:%S")
    seen, refused, done, other, slowest = [], [], None, [], []
    totals = Counter()
    uses, declares = Counter(), []
    with open(record_path, "a") as record:
        for line in proc.stdout:
            line = line.rstrip("\n")
            if not line.startswith("{"):
                if line.strip():
                    other.append(line)
                continue
            r = json.loads(line)
            if r.get("done"):
                done = r
                continue
            b = r["bundle"]
            k = len(seen)
            seen.append(b)
            if k >= len(names) or names[k] != b:
                raise SystemExit("the pass answered for %s where %s was due" % (b, names[min(k, len(names) - 1)]))
            for key in ("constants", "known", "skipped", "absent", "refused", "check_ms", "n_slow"):
                totals[key] += r.get(key, 0)
            slowest = sorted(slowest + [(ms, n, b) for n, ms in r.get("slow", [])], reverse=True)[:12]
            for a in r["uses"]:
                uses[a] += 1
            declares += [(b, a) for a in r["declares"]]
            if k >= trusted:
                r.update(sig=sig[b], chain=chain[b], run=pass_id)
                record.write(json.dumps(r, ensure_ascii=False) + "\n")
                record.flush()
            if not r["ok"]:
                refused.append(b)
                print("   REFUSED %s, %d constants: %s" % (b, r["refused"], json.dumps(r["errors"][:3], ensure_ascii=False)[:900]),
                      flush=True)
            if (k + 1) % 50 == 0:
                print("%d bundles, %d constants, %d refused, %.0f s" % (k + 1, totals["constants"], len(refused),
                                                                        time.time() - t0), flush=True)
    code = proc.wait()
    changed = [b for b in names if stamp(b) != stamps[b]]
    print("%d of %d bundles in %.0f s: %d constants, of them %d theorems that were there already; %d unsafe or "
          "partial constants left out" % (len(seen), len(names), time.time() - t0, totals["constants"], totals["known"],
                                          totals["skipped"]))
    print("the checks took %.1f hours of one thread; %d of them 5 s or more%s"
          % (totals["check_ms"] / 3.6e6, totals["n_slow"],
             (", the longest: " + ", ".join("%s %.0f s (%s)" % (n, ms / 1000, b) for ms, n, b in slowest[:6]))
             if slowest else ""))
    print("axioms that the bundles declare: %s" % (" ".join("%s (%s)" % (a, b) for b, a in declares[:20]) or "none"))
    print("axioms below the build that its constants name (bundles): %s"
          % (", ".join("%s (%d)" % (a, n) for a, n in sorted(uses.items())) or "none"))
    odd = sorted(a for a in uses if a not in STANDARD)
    if odd:
        print("   of them not one of the three standard axioms: %s" % " ".join(odd))
    if totals["absent"]:
        print("imports named in a bundle's header that are no longer bundles of the build: %d (the constants are "
              "what counts, and the kernel looked for each)" % totals["absent"])
    if other:
        print("the pass also said: " + " | ".join(other)[-1500:])
    if changed:
        print("CHANGED under the pass, run it again: %s" % " ".join(changed[:20]))
    whole = done is not None and len(seen) == len(names) and code == 0
    if not whole and not refused:
        print("the pass stopped before its end (exit %s); run it again, it goes on from the last bundle accepted"
              % code)
    print("refused: %s" % (" ".join(refused) or "none"))
    final = whole and not refused and not changed and not declares and not odd
    if final and not args.max_level:
        print("the kernel accepts every constant of the build over the outside modules; no bundle declares an "
              "axiom, and no constant of the build names one but the three standard axioms (what a theorem rests on "
              "through the outside modules: bundle_check.py)")
    raise SystemExit(0 if final else 1)


if __name__ == "__main__":
    main()
