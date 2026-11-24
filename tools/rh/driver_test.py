#!/usr/bin/env python3
"""Run the small jobs that pin down what `lean/Bundle.lean` does.

    python3 tools/rh/driver_test.py [--driver PATH] [--workspace DIR ...]

Every job of the archive's build reads `lean/Bundle.lean` when it starts, so the file is never edited in place
while a build runs: a change is made on a copy, this script is run on the copy (`--driver`), and the copy then
replaces the file with `mv`. Each job below is two or three files of a few lines (`lean/tests/`), compiled as
one bundle, and stands for one thing that a bundle of the archive got wrong before the driver learned it; the
number after it is how many of its files must end with an error. The driver has to compile under the archive's
toolchain and the library's, so each job runs in both workspaces by default.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

# (what it is about, imports, fields of the job, [(file, module, fields of the file)], files that must fail);
# an import `T.pre` is the bundle of the files U1 and U2, compiled first
JOBS = [
    ("`open private a from M` for a file of the same bundle", ["Batteries.Tactic.OpenPrivate"], {},
     [("A", "A", {}), ("B", "B", {})], 0),
    ("a pin to a private name of the file itself", [], {},
     [("C", "C", {}), ("D", "Some.Mod.D", {"rewrite": [["4", "5", "pick", "_private_.Low.Inner.pick", "n"]]})], 0),
    ("a pin that is a choice of two constants", [], {},
     [("E", "E", {}), ("G", "G", {"rewrite": [["2", "3", "pick", "_root_.A.pick|_root_.B.pick", "c"]]})], 0),
    ("`open N (a b)` with names that are not there: some of the list, and all of it", [], {},
     [("E", "E", {}), ("H", "H", {"rewrite": [["3", "3", "pick", "_root_.A.pick", "n"]]})], 0),
    ("`open N (a b)` with a name that `export` put there, and one that is not there", [], {},
     [("E2", "E2", {}), ("H2", "H2", {})], 0),
    ("a declaration compiled under another name: its recursive calls, and a use that is pinned to it", [], {},
     [("C2", "C2", {}), ("D2", "D2", {"rename": [["dup", "dup_b2", "decl"], ["loop", "loop_b2", "decl"]],
                                      "rewrite": [["5", "5", "loop", "_root_.NS.loop_b2", "n"]]})], 0),
    ("the rename reaches a use through the type of a term (`a.dup`), and no other name that ends alike", [], {},
     [("C2", "C2", {}), ("D3", "D3", {"rename": [["dup", "dup_b2", "decl"]]})], 0),
    ("a pin does not replace a binder of that name", [], {},
     [("K", "K", {}), ("K2", "K2", {"rewrite": [["0", "9", "G", "_root_.A2.G", "n"]]})], 0),
    ("each file names its lifted proofs as it does alone", [], {},
     [("P1", "P1", {}), ("P2", "P2", {"thm": [[1, 1]]})], 0),
    ("with `shareProofs` the second file uses the first one's lifted proof and has none of its own", [],
     {"shareProofs": True}, [("P1", "P1", {}), ("P2", "P2", {"thm": [[1, 1]]})], 1),
    ("`open N (a b)` that finds one constant twice, or lists a name that is not there, also before `in`", [], {},
     [("Q1", "Q1", {}), ("Q2", "Q2", {"thm": [[2, 2], [5, 5]]})], 0),
    ("a pin leaves the name of a field and of a named argument alone", [], {},
     [("R1", "R1", {}), ("R2", "R2", {"thm": [[4, 4], [5, 5]], "rewrite": [["0", "9", "cpt", "_root_.NS.cpt", "n"]]})],
     0),
    ("a field of a `structure` named like a constant: pinned in its own type, the field from the next one on", [], {},
     [("S1", "S1", {}), ("S2", "S2", {"thm": [[6, 6]], "rewrite": [["0", "9", "twist", "_root_.NS.twist", "n"]]})],
     0),
    ("a file's own `maxHeartbeats` is raised: the limit that fits the file alone is too low in a bundle", [], {},
     [("V1", "V1", {}), ("V2", "V2", {"thm": [[1, 2], [3, 5]]})], 0),
    ("two instances of one key from the bundle below: the one declared last is tried first", ["T.pre"], {},
     [("U3", "U3", {"thm": [[0, 0]]})], 1),
    ("… and in the order of the file's own imports when the job gives it", ["T.pre"], {},
     [("U3", "U3", {"thm": [[0, 0]], "instOrder": [[["tagB", "0"], ["tagA", "1"]]]})], 0),
]
PRE = [("U1", "U1", {}), ("U2", "U2", {})]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--driver", default=os.path.join(HERE, "lean", "Bundle.lean"))
    ap.add_argument("--workspace", nargs="*",
                    default=[os.path.join(REPO, "external", "alpoge-rh", "native-ws"), REPO])
    args = ap.parse_args()
    driver = os.path.abspath(args.driver)
    src = os.path.join(HERE, "lean", "tests")
    failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        for ws in args.workspace:
            if not os.path.isdir(ws):
                print("no workspace %s: skipped" % ws)
                continue
            lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                                  check=True).stdout.strip()
            lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True,
                                       text=True, check=True).stdout.strip()
            env = dict(os.environ, LEAN_PATH=tmp + os.pathsep + lean_path)
            os.makedirs(os.path.join(tmp, "T"), exist_ok=True)

            def run(name, olean, imports, extra, files):
                job = dict(name=name, olean=olean, log=os.path.join(tmp, "t.log"), imports=imports, options=[],
                           slowOptions=[], rollback=True, files=[])
                job["async"] = True
                job.update(extra)
                for fname, module, fields in files:
                    row = dict(path=os.path.join(src, fname + ".lean"), module=module, skip=[], thm=[], slow=False)
                    row.update(fields)
                    job["files"].append(row)
                path = os.path.join(tmp, "job.json")
                with open(path, "w") as f:
                    json.dump(job, f)
                if os.path.exists(job["log"]):
                    os.remove(job["log"])
                p = subprocess.run([lean, "--run", driver, path], cwd=ws, capture_output=True, text=True, env=env)
                bad = None
                for line in p.stdout.split("\n"):
                    if line.startswith('{"done"'):
                        bad = json.loads(line)["bad"]
                return bad, p, job

            bad, p, _ = run("T.pre", os.path.join(tmp, "T", "pre.olean"), [], {}, PRE)
            if bad != 0:
                failed += 1
                print("FAIL  %-14s the bundle that two jobs import\n%s" % (os.path.basename(ws.rstrip("/")),
                                                                         (p.stdout + p.stderr)[-1500:]))
            for k, (what, imports, extra, files, want) in enumerate(JOBS):
                bad, p, job = run("T.t%d" % k, os.path.join(tmp, "t.olean"), imports, extra, files)
                ok = bad == want
                failed += not ok
                print("%s  %-14s %s (files with an error: %s, to be %d)"
                      % ("ok  " if ok else "FAIL", os.path.basename(ws.rstrip("/")), what, bad, want), flush=True)
                if not ok:
                    print((p.stdout + p.stderr)[-1500:])
                    if os.path.exists(job["log"]):
                        with open(job["log"], errors="replace") as f:
                            print(f.read()[-1500:])
    print("%d failed" % failed)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
