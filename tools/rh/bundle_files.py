#!/usr/bin/env python3
"""Compile a Lean file and the files it imports on another pin, and list every error at once.

    python3 -I tools/rh/bundle_files.py --src ROOT --out OUT --workspace WS TARGET [TARGET ...]
        [--prelude FILE.lean] [--simp-out LIST.json] [--with OUT_OF_A_BUNDLE_BUILD] [--option name=bool:false ...]
        [--jobs N] [--threads N] [--retry] [--deep] [--again MODULE] [--check MODULE] [--dry-run]

ROOT holds the sources (`A/B.lean` is the module `A.B`); a TARGET is a module of ROOT, or the path of a `.lean`
file elsewhere that imports modules of ROOT. WS is a Lake workspace whose
toolchain and packages are used. Every file that the targets reach by imports is compiled in its own process by
`lean/Bundle.lean`, under its own module name and with its own imports, to OUT/olean. An import that is not under
ROOT is imported as it is, except that a file that imports any part of Mathlib imports all of it (a part may not
exist at another pin).

It is for a port. `lean` writes nothing for a file with an error, so a build stops at the first layer of failures;
`Bundle.lean` writes the file's declarations all the same, a theorem whose proof failed among them, so one run
shows every declaration that fails. OUT/errors.json has them (module, line, column, message), OUT/errors.txt the
same to read.

`--prelude` names a file that is compiled first and imported by every file: the names that the pin lacks.

`--simp-out` names a list of simp lemmas that no file is to have in its simp set (`simp_diff.py`: those that the
pin marks `@[simp]` and the pin that the files were written for does not).

`--with` names the output of `bundle_build.py`: the targets, and only they, import its bundles too, so that a
target can join what the archive proves to what ROOT proves. The files of ROOT do not see the archive.

`--check MODULE` (it may be given several times) compiles that module only, against what OUT already has of its imports, prints the
errors with the lines around them, and records nothing: for a file being worked on while a run is going on.

Run again after a change: a file is compiled again when its text changed, `--retry` adds the files with errors,
`--again MODULE` the module named. The files that import a changed file are not compiled again unless `--deep` is given.
That is right while only proofs change, and it leaves files compiled against an earlier state of what they
import: the run counts them, and a result is to be trusted only after a run with `--deep` that leaves none.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
MESSAGE = re.compile(r"^(/.*?\.lean):(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: (.*)$")
WHOLE = ("Mathlib", "Batteries", "Lean", "Std", "Init", "Aesop", "Qq", "Plausible", "ProofWidgets")


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read_errors(log):
    """The errors of a log of `Bundle.lean`: [line, column, message], the message whole."""
    out, cur = [], None
    if not os.path.exists(log):
        return out
    with open(log, errors="replace") as f:
        for line in f:
            m = MESSAGE.match(line.rstrip("\n"))
            if m:
                cur = None
                if m.group(4) == "error":
                    cur = [int(m.group(2)), int(m.group(3)), m.group(5)]
                    out.append(cur)
            elif cur is not None:
                cur[2] += "\n" + line.rstrip("\n")
    for e in out:
        e[2] = e[2].rstrip()[:6000]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--workspace", required=True)
    ap.add_argument("--prelude", help="a file compiled first and imported by every file")
    ap.add_argument("--with", dest="base", help="the output of bundle_build.py; the targets import its bundles")
    ap.add_argument("--option", action="append", default=[], help="name=bool:true or name=nat:400000")
    ap.add_argument("--simp-out", help="a JSON list of [name, post, inv]: simp lemmas to take out of the simp set "
                                       "of every file (simp_diff.py)")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--threads", type=int, default=3)
    ap.add_argument("--retry", action="store_true", help="compile the files with errors again")
    ap.add_argument("--deep", action="store_true", help="compile again what imports a file compiled again")
    ap.add_argument("--again", action="append", default=[], help="a module to compile again")
    ap.add_argument("--check", action="append", default=[],
                    help="compile this module only, against what OUT has, print its errors, record nothing")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("targets", nargs="+")
    args = ap.parse_args()
    ba, bb = load("build_archive"), load("bundle_build")
    src, out = os.path.abspath(args.src), os.path.abspath(args.out)
    for d in ("olean", "job", "log"):
        os.makedirs(os.path.join(out, d), exist_ok=True)
    path = {}
    for root, dirs, files in os.walk(src):
        dirs.sort()
        for name in files:
            if name.endswith(".lean"):
                p = os.path.join(root, name)
                path[os.path.relpath(p, src)[:-5].replace(os.sep, ".")] = p
    extra_dirs = []
    for k, t in enumerate(args.targets):
        if t.endswith(".lean"):
            # a target outside ROOT, by its path
            name = os.path.basename(t)[:-5]
            path[name] = os.path.abspath(t)
            extra_dirs.append(os.path.dirname(path[name]))
            args.targets[k] = name
    prelude = None
    if args.prelude:
        prelude = os.path.basename(args.prelude)[:-5]
        path[prelude] = os.path.abspath(args.prelude)
    imports, outside, text_of = {}, {}, {}
    stack = list(args.targets) + ([prelude] if prelude else [])
    while stack:
        m = stack.pop()
        if m in imports:
            continue
        with open(path[m], encoding="utf-8") as f:
            text_of[m] = f.read()
        imports[m], outside[m] = [], []
        for i in ba.header(text_of[m]):
            if i in path and i != prelude:
                imports[m].append(i)
                stack.append(i)
            elif i != prelude:
                outside[m].append(i)
        if prelude and m != prelude:
            imports[m].append(prelude)
    for m in imports:
        ext = outside[m]
        if any(i == "Mathlib" or i.startswith("Mathlib.") for i in ext):
            ext = ["Mathlib"] + [i for i in ext if i.split(".")[0] not in WHOLE]
        outside[m] = sorted(set(ext))
    # the order: a file after what it imports
    order, state_of = [], {}
    for m in sorted(imports):
        todo = [m]
        while todo:
            x = todo[-1]
            if state_of.get(x) == 2:
                todo.pop()
                continue
            missing = [i for i in imports[x] if state_of.get(i) != 2]
            if missing and state_of.get(x) != 1:
                state_of[x] = 1
                todo.extend(missing)
            else:
                state_of[x] = 2
                order.append(x)
                todo.pop()
    lines = {m: text_of[m].count("\n") + 1 for m in imports}
    print("%d files, %d lines" % (len(imports), sum(lines.values())), flush=True)
    if args.dry_run:
        return
    options = [["linter.all", "bool", "false"]]
    for o in args.option:
        name, value = o.split("=", 1)
        kind, value = value.split(":", 1)
        options.append([name, kind, value])
    ws = os.path.abspath(args.workspace)
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, capture_output=True, text=True,
                               check=True).stdout.strip()
    lean = subprocess.run(["lake", "env", "which", "lean"], cwd=ws, capture_output=True, text=True,
                          check=True).stdout.strip()
    search = [os.path.join(out, "olean")]
    base_imports = []
    readable = [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), src, out, HERE] + \
               ([os.path.dirname(path[prelude])] if prelude else []) + extra_dirs
    if args.base:
        base = os.path.abspath(args.base)
        search.append(os.path.join(base, "olean"))
        readable.append(base)
        last = {}
        with open(os.path.join(base, "state.jsonl")) as f:
            for line in f:
                r = json.loads(line)
                last[r["bundle"]] = r
        base_imports = ["B." + b for b in sorted(last) if last[b]["ok"]]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(search + [lean_path]))
    profile = os.path.join(out, "sandbox.sb")
    with open(profile, "w") as f:
        f.write(bb.sandbox_profile(out, readable))
    state_path = os.path.join(out, "state.json")
    state = {}
    if os.path.exists(state_path):
        with open(state_path) as f:
            state = json.load(f)
    digest = {m: hashlib.sha1(text_of[m].encode()).hexdigest() for m in imports}

    def olean(m):
        return os.path.join(out, "olean", *m.split(".")) + ".olean"

    def stale(m):
        """Whether a file was compiled against another state of an import than the one there now."""
        s = state.get(m)
        return bool(s) and any(state.get(i, {}).get("stamp") != s["seen"].get(i) for i in imports[m])

    def needs(m):
        s = state.get(m)
        if not s or s["sha"] != digest[m] or not os.path.exists(olean(m)) or m in args.again:
            return True
        if args.retry and (s["errors"] or not s["ok"]):
            return True
        return args.deep and (stale(m) or sorted(s["seen"]) != sorted(imports[m]))

    leak = []
    if args.simp_out:
        with open(args.simp_out, encoding="utf-8") as f:
            leak = [dict(inst=[], simp=json.load(f))]

    def with_view(job, m):
        # the prelude is compiled with the simp set as it is: it is what adds to it
        if leak and m != prelude:
            job["leak"], job["eraseAll"] = leak, [0]
        return job

    if args.check:
        # a file being worked on: its own process, beside a run that may be going on, and nothing of OUT changed
        os.makedirs(os.path.join(out, "check"), exist_ok=True)
        for m in args.check:
            job = dict(name=m, olean=os.path.join(out, "check", m + ".olean"),
                       log=os.path.join(out, "check", m + ".log"),
                       imports=outside[m] + (base_imports if m in args.targets else []) + imports[m],
                       options=options, slowOptions=[], rollback=False, files=[
                           dict(path=path[m], module=m, skip=[], thm=[], slow=False)])
            job["async"] = True
            with_view(job, m)
            jp = os.path.join(out, "check", m + ".json")
            with open(jp, "w") as f:
                json.dump(job, f)
            for p in (job["olean"], job["log"]):
                if os.path.exists(p):
                    os.remove(p)
            t = time.time()
            r = subprocess.run(["/usr/bin/sandbox-exec", "-f", profile, lean, "-j", str(args.threads),
                                "--tstack=400000", "--run", os.path.join(HERE, "lean", "Bundle.lean"), jp],
                               capture_output=True, text=True, env=env)
            errors = read_errors(job["log"])
            text = text_of[m].split("\n")
            print("== %s: %d errors, %.0f s%s" % (m, len(errors), time.time() - t,
                                                 "" if r.returncode == 0 else "; the process died: " + r.stdout[-800:]))
            for line, col, msg in errors:
                print("-- %s:%d:%d" % (m, line, col))
                for k in range(max(0, line - 3), min(len(text), line + 2)):
                    print("%s%5d  %s" % (">" if k == line - 1 else " ", k + 1, text[k]))
                print("   " + msg[:2500].replace("\n", "\n   "))
        return

    def start(m):
        job = dict(name=m, olean=olean(m), log=os.path.join(out, "log", m + ".log"),
                   imports=outside[m] + (base_imports if m in args.targets else []) + imports[m],
                   options=options, slowOptions=[], rollback=False, files=[
                       dict(path=path[m], module=m, skip=[], thm=[], slow=False)])
        job["async"] = True
        with_view(job, m)
        jp = os.path.join(out, "job", m + ".json")
        with open(jp, "w") as f:
            json.dump(job, f)
        os.makedirs(os.path.dirname(job["olean"]), exist_ok=True)
        for p in (job["olean"], job["log"]):
            if os.path.exists(p):
                os.remove(p)
        o = open(os.path.join(out, "log", m + ".out"), "w")
        cmd = ["/usr/bin/sandbox-exec", "-f", profile, lean, "-j", str(args.threads), "--tstack=400000", "--run",
               os.path.join(HERE, "lean", "Bundle.lean"), jp]
        return dict(job=job, proc=subprocess.Popen(cmd, stdout=o, stderr=subprocess.STDOUT, env=env), o=o,
                    t=time.time())

    t0 = time.time()
    done, running, blocked, died, compiled = set(), {}, set(), set(), 0
    waiting = list(order)
    total = sum(1 for m in order if needs(m)) if not args.deep else None
    print("to compile: %s" % (total if total is not None else "what changed and what imports it"), flush=True)
    while waiting or running:
        for m in list(waiting):
            if len(running) >= args.jobs:
                break
            if any(i in blocked for i in imports[m]):
                blocked.add(m)
                waiting.remove(m)
                continue
            if not all(i in done for i in imports[m]):
                continue
            waiting.remove(m)
            if needs(m):
                running[m] = start(m)
            else:
                done.add(m)
        finished = [m for m, r in running.items() if r["proc"].poll() is not None]
        if not finished:
            time.sleep(0.2)
            continue
        for m in finished:
            r = running.pop(m)
            r["o"].close()
            errors = read_errors(r["job"]["log"])
            ok = r["proc"].returncode == 0 and os.path.exists(r["job"]["olean"])
            if not ok:
                with open(os.path.join(out, "log", m + ".out")) as f:
                    errors.append([0, 0, "the process died: " + f.read()[-1500:]])
                blocked.add(m)
                died.add(m)
            else:
                done.add(m)
            compiled += 1
            state[m] = dict(sha=digest[m], errors=errors, ok=ok, stamp="%s@%.3f" % (digest[m][:12], time.time()),
                            seen={i: state.get(i, {}).get("stamp") for i in imports[m]},
                            s=round(time.time() - r["t"], 1))
            with open(state_path + ".tmp", "w") as f:
                json.dump(state, f)
            os.replace(state_path + ".tmp", state_path)
            print("[%d] %-44s %4d errors  %6.1f s   (%.0f s)" % (compiled, m, len(errors), state[m]["s"],
                                                                time.time() - t0), flush=True)
    errors = [[m, e[0], e[1], e[2]] for m in order for e in state.get(m, {}).get("errors", [])]
    with open(os.path.join(out, "errors.json"), "w") as f:
        json.dump(errors, f, indent=1, ensure_ascii=False)
    with open(os.path.join(out, "errors.txt"), "w") as f:
        for m, line, col, msg in errors:
            f.write("%s:%d:%d: %s\n\n" % (os.path.relpath(path[m], src), line, col, msg))
    files = Counter(e[0] for e in errors)
    kinds = Counter(re.sub(r"`[^`]*`|'[^']*'|\d+", "…", e[3].split("\n")[0])[:60] for e in errors)
    print("%d compiled; %d errors in %d files of %d; %d files not compiled for a failed import; "
          "%d compiled against an earlier state of an import"
          % (compiled, len(errors), len(files), len(imports), len(blocked - died),
             sum(1 for m in order if stale(m))))
    for k, v in kinds.most_common(25):
        print("  %5d  %s" % (v, k))


if __name__ == "__main__":
    main()
