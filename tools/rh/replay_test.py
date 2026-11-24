#!/usr/bin/env python3
"""Run the small cases that pin down what the kernel pass refuses (`lean/ReplayAll.lean`, `bundle_replay.py`).

    python3 tools/rh/replay_test.py [--workspace DIR]

A check that has only ever said yes proves nothing about itself. This compiles five files of a few lines
(`lean/tests/replay/`), has `lean/Tamper.lean` change one constant in a compiled file (a proof, a statement, the
body of a definition, a theorem made an axiom, a proof taken away), and runs the pass on each set: it must accept
the files as they were compiled and refuse, by name, exactly the constants that no longer hold. The last cases
run `bundle_replay.py` on a made-up build of three bundles: a second pass has nothing to check, and after a
change to the middle bundle it checks that one and the one after it, and not the first.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
TESTS = os.path.join(HERE, "lean", "tests", "replay")

# (what it is about, the files in order, the change (file, how, A, B) or None,
#  {file: the constants that must be refused}, what else must hold of the lines)
CASES = [
    ("the files as they were compiled", ["RA1", "RA2b", "RA2"], None, {}, {"known": 1}),
    ("a theorem with the proof of another", ["RA1", "RA2"], ("RA1", "proof", "RA.double_two", "RA.triple_two"),
     {"RA1": ["RA.double_two"]}, {}),
    ("a statement changed below a proof that uses it", ["RA1", "RA2"],
     ("RA1", "statement", "RA.double_two", "RA.triple_two"), {"RA1": ["RA.double_two"], "RA2": ["RA.four"]}, {}),
    ("a definition with another body, below a proof that computes it", ["RA1", "RA2"],
     ("RA1", "body", "RA.double", "RA.triple"), {"RA1": ["RA.double_two"]}, {}),
    ("a proof that is not there", ["RA1", "RA2"], ("RA1", "gone", "RA.size_pos", "RA.size_pos"),
     {"RA1": ["RA.size_pos"]}, {}),
    ("a theorem made an axiom", ["RA1", "RA2"], ("RA1", "axiom", "RA.double_two", "RA.double_two"), {},
     {"declares": ["RA.double_two"]}),
    ("a proof by `sorry`", ["RA1", "RA3"], None, {}, {"uses": ["sorryAx"]}),
    ("a name of the bundle below with another statement", ["RA1", "RA2c"], None, {"RA2c": ["RA.common"]}, {}),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", default=os.path.join(REPO, "external", "alpoge-rh", "native-ws"))
    args = ap.parse_args()
    ws = os.path.abspath(args.workspace)
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True, text=True,
                               check=True).stdout.strip()
    tmp = tempfile.mkdtemp(prefix="replay-test-")
    env = dict(os.environ, LEAN_PATH=tmp + os.pathsep + lean_path)
    failed = 0
    try:
        # the files are the modules `B.RA1` …, as the bundles of a build are `B.l001n000` …
        mods = os.path.join(tmp, "B")
        os.makedirs(mods)
        for name in ("RA1", "RA2", "RA2b", "RA2c", "RA3"):
            p = subprocess.run([lean, "-o", os.path.join(mods, name + ".olean"), os.path.join(TESTS, name + ".lean")],
                               capture_output=True, text=True, env=env)
            if p.returncode != 0:
                raise SystemExit("%s.lean does not compile: %s" % (name, (p.stdout + p.stderr)[-600:]))

        def run_pass(rows):
            job = os.path.join(tmp, "job.json")
            with open(job, "w") as f:
                json.dump(dict(imports=["Init"], bundles=rows, window=100), f)
            p = subprocess.run([lean, "-j", "2", "--tstack=400000", "--run", os.path.join(HERE, "lean", "ReplayAll.lean"),
                                job], capture_output=True, text=True, env=env)
            lines = [json.loads(x) for x in p.stdout.split("\n") if x.startswith("{")]
            return p, {r["bundle"]: r for r in lines if "bundle" in r}

        for about, files, change, refused, more in CASES:
            path = {f: os.path.join(mods, f + ".olean") for f in files}
            if change:
                f, how, a, b = change
                path[f] = os.path.join(tmp, f + "-changed.olean")
                p = subprocess.run([lean, "--run", os.path.join(HERE, "lean", "Tamper.lean"),
                                    os.path.join(mods, f + ".olean"), path[f], how, a, b], capture_output=True,
                                   text=True, env=env)
                if p.returncode != 0:
                    raise SystemExit("Tamper.lean failed: " + (p.stdout + p.stderr)[-600:])
            p, got = run_pass([[f, path[f], "check"] for f in files])
            wrong = []
            if sorted(got) != sorted(files):
                wrong.append("lines for %s; the pass said: %s" % (sorted(got), (p.stdout + p.stderr)[-400:]))
            for f in files:
                r = got.get(f)
                if r is None:
                    continue
                names = sorted(e[0] for e in r["errors"])
                if names != sorted(refused.get(f, [])):
                    wrong.append("%s: refused %s, and %s was due" % (f, names, sorted(refused.get(f, []))))
                if r["ok"] != (not refused.get(f)):
                    wrong.append("%s: ok is %s" % (f, r["ok"]))
            for key, value in more.items():
                have = [r[key] for r in got.values()]
                total = sum(have) if isinstance(value, int) else sorted(x for xs in have for x in xs)
                if total != value:
                    wrong.append("%s is %s, and %s was due" % (key, total, value))
            if (p.returncode == 0) != (not refused):
                wrong.append("exit status %d" % p.returncode)
            print("%-4s %s%s" % ("ok" if not wrong else "FAIL", about, "".join("\n       " + w for w in wrong)))
            failed += bool(wrong)

        # `bundle_replay.py` on a build of three bundles
        out = os.path.join(tmp, "build")
        os.makedirs(os.path.join(out, "olean", "B"))
        order = [("l001n000", "RA1", 1), ("l001n001", "RA2b", 1), ("l002n000", "RA2", 2)]
        with open(os.path.join(out, "state.jsonl"), "w") as f:
            for b, src, level in order:
                shutil.copy(os.path.join(mods, src + ".olean"), os.path.join(out, "olean", "B", b + ".olean"))
                f.write(json.dumps(dict(bundle=b, level=level, files=[0], ok=True, errors=[])) + "\n")
        scan = os.path.join(tmp, "scan.json")
        with open(scan, "w") as f:
            json.dump(dict(external={"Init": 1}), f)

        def replay(*more):
            p = subprocess.run([sys.executable, "-I", os.path.join(HERE, "bundle_replay.py"), "--out", out, "--scan",
                                scan, "--workspace", ws, "--threads", "2"] + list(more), capture_output=True,
                               text=True, env=env)
            return p.returncode, p.stdout + p.stderr

        def records():
            with open(os.path.join(out, "replay.jsonl")) as f:
                return [json.loads(x) for x in f]

        steps = []
        code, text = replay()
        steps.append(("a first pass checks the three bundles and accepts them",
                      code == 0 and [r["bundle"] for r in records()] == [b for b, _, _ in order]
                      and "3 to check" in text, text))
        code, text = replay()
        steps.append(("a second pass has nothing to check", code == 0 and len(records()) == 3
                      and "0 to check" in text, text))
        # the middle bundle is written again: the same constants at other addresses, so other bytes
        subprocess.run([lean, "--run", os.path.join(HERE, "lean", "Tamper.lean"), os.path.join(mods, "RA2b.olean"),
                        os.path.join(out, "olean", "B", "l001n001.olean"), "proof", "RA.common", "RA.common"],
                       check=True, env=env, capture_output=True)
        code, text = replay()
        steps.append(("after a change to the second bundle the pass checks it and the third, not the first",
                      [r["bundle"] for r in records()][3:] == ["l001n001", "l002n000"] and "2 to check" in text, text))
        # … and a wrong proof in the first is refused, and the pass is not final
        subprocess.run([lean, "--run", os.path.join(HERE, "lean", "Tamper.lean"), os.path.join(mods, "RA1.olean"),
                        os.path.join(out, "olean", "B", "l001n000.olean"), "proof", "RA.double_two", "RA.triple_two"],
                       check=True, env=env, capture_output=True)
        code, text = replay()
        steps.append(("a wrong proof in the first bundle: refused, and everything is checked again",
                      code == 1 and "REFUSED l001n000" in text and "3 to check" in text, text))
        for about, good, text in steps:
            print("%-4s %s%s" % ("ok" if good else "FAIL", about, "" if good else "\n       " + text[-900:]))
            failed += not good
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    print("%d failed" % failed)
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
