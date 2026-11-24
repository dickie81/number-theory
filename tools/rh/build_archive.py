#!/usr/bin/env python3
"""Compile the archive's modules with `lean`, in the order of their imports, and record what happens to each.

    python3 -I tools/rh/build_archive.py [--jobs N] [--targets Main] [--max-level L] [--limit K] [--sandbox]

The archive is the claimed proof of the Riemann Hypothesis that tools/rh/fetch_archive.sh fetches. It pins
Lean v4.33.1 and a Mathlib of August 2026; this script compiles it against this repository's toolchain and
Mathlib by default, so that its theorems can be imported here; `--workspace DIR` compiles it against the
toolchain and packages of another Lake workspace (one on the archive's own pins, for instance). It does not use
the archive's lakefile or Lake: it runs `lean` on each file with the options that lakefile sets, with LEAN_PATH
pointing at the workspace's packages (`lake exe cache get` first) and at its own output directory.

* The build is resumable. A module is compiled again only if its source, its options or one of its imports
  changed (the trace is a hash of those). `OUT/status.jsonl` holds one line for each compile.
* A module that fails blocks the modules that import it; the others go on. `OUT/fail/<module>.log` holds the
  output of a failed compile. The summary at the end lists the failures by how many modules each blocks.
* `--overlay DIR` takes `DIR/<path>.lean` in place of the archive's file where it exists: the port's patched
  files. The archive itself is never edited.
* `--sandbox` (macOS) runs each compile under `sandbox-exec`: no network, and no writes outside OUT. The
  archive is untrusted code, and elaborating Lean runs its tactics and macros.

Paths: --src external/alpoge-rh/extract/lean/src, --out external/alpoge-rh/build (both under .gitignore).
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import threading
import time
from collections import Counter, defaultdict, deque

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+|runtime\s+)?(.*)$")

# The options of the archive's lakefile.toml.
LEAN_ARGS = ["--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3",
             "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]
# Its library GroundTheoryFields adds one option.
FIELDS = ("GroundTheory.LocalFields.", "GroundTheory.GlobalFields.")
FIELDS_ARGS = ["-DsynthInstance.maxHeartbeats=400000"]


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
        if s == "" or s == "module" or s.startswith("--") or s.startswith("prelude"):
            continue
        break
    return imports


def index(src, overlay, cache_path):
    """For each module: its source file, the hash of the source, and its imports. Cached by size and mtime."""
    try:
        with open(cache_path) as f:
            cache = json.load(f)
    except (OSError, ValueError):
        cache = {}
    mods, fresh = {}, {}
    for root, dirs, files in os.walk(src):
        dirs.sort()
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(root, name)
            rel = os.path.relpath(path, src)
            if overlay and os.path.exists(os.path.join(overlay, rel)):
                path = os.path.join(overlay, rel)
            st = os.stat(path)
            key = [path, st.st_size, st.st_mtime_ns]
            old = cache.get(rel)
            if old and old[0] == key:
                entry = old
            else:
                with open(path, "rb") as f:
                    raw = f.read()
                entry = [key, hashlib.sha1(raw).hexdigest(), header(raw.decode("utf-8", "replace")), raw.count(b"\n")]
            fresh[rel] = entry
            mods[rel[:-5].replace(os.sep, ".")] = {"path": path, "hash": entry[1], "imports": entry[2], "lines": entry[3]}
    with open(cache_path, "w") as f:
        json.dump(fresh, f)
    return mods


def sandbox_profile(out, readable):
    """No network; writes only under OUT; of the home directory, only what a compile needs is readable."""
    home = os.path.expanduser("~")
    lines = ["(version 1)", "(allow default)", "(deny network*)", "(deny file-write*)",
             '(allow file-write* (subpath "%s") (literal "/dev/null") (literal "/dev/stdout") (literal "/dev/stderr"))' % out,
             '(deny file-read* (subpath "%s"))' % home]
    for p in readable:
        lines.append('(allow file-read* (subpath "%s"))' % p)
    # a process may always read the directories that lead to what it may read
    seen = set()
    for p in readable:
        d = os.path.dirname(p)
        while d.startswith(home) and d not in seen:
            seen.add(d)
            lines.append('(allow file-read-metadata (literal "%s"))' % d)
            d = os.path.dirname(d)
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default=os.path.join(ROOT, "external/alpoge-rh/extract/lean/src"))
    ap.add_argument("--out", default=os.path.join(ROOT, "external/alpoge-rh/build"))
    ap.add_argument("--overlay", default=None)
    ap.add_argument("--workspace", default=ROOT,
                    help="the Lake workspace whose toolchain and packages to compile against (default: this repository)")
    ap.add_argument("--lean-args", default=None,
                    help="options for `lean` in place of the archive's (to compile another source tree with this script)")
    ap.add_argument("--shuffle", type=int, default=None, help="compile the modules that are ready at the start in a random order (seed)")
    ap.add_argument("--targets", nargs="*", default=["Main"])
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 2))
    ap.add_argument("--threads", type=int, default=None, help="lean's -j for each compile (default: lean's own)")
    ap.add_argument("--max-level", type=int, default=None, help="only modules up to this depth of the import graph")
    ap.add_argument("--limit", type=int, default=None, help="stop after this many compiles")
    ap.add_argument("--timeout", type=int, default=7200, help="seconds for one compile")
    ap.add_argument("--sandbox", action="store_true")
    ap.add_argument("--dry-run", action="store_true", help="say what would be compiled and stop")
    args = ap.parse_args()

    src, out = os.path.abspath(args.src), os.path.abspath(args.out)
    overlay = os.path.abspath(args.overlay) if args.overlay else None
    lib, fail_dir, cwd = os.path.join(out, "lib"), os.path.join(out, "fail"), os.path.join(out, "cwd")
    for d in (lib, fail_dir, cwd):
        os.makedirs(d, exist_ok=True)

    # the toolchain and the packages of this repository
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    ws = os.path.abspath(args.workspace)
    lean = subprocess.run(["elan", "which", "lean"], cwd=ws, env=env, capture_output=True, text=True, check=True).stdout.strip()
    version = subprocess.run([lean, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    repo_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ws, env=env, capture_output=True, text=True,
                               check=True).stdout.strip()
    lean_path = lib + os.pathsep + repo_path
    mathlib_rev = subprocess.run(["git", "-C", os.path.join(ws, ".lake/packages/mathlib"), "rev-parse", "HEAD"],
                                 capture_output=True, text=True).stdout.strip()

    t0 = time.time()
    mods = index(src, overlay, os.path.join(out, "index.json"))
    print("%d modules indexed in %.0f s; %s; Mathlib %s" % (len(mods), time.time() - t0, version, mathlib_rev[:12]), flush=True)

    # the closure of the targets, and each module's level
    closure, todo = set(), [t for t in args.targets if t in mods]
    missing_targets = [t for t in args.targets if t not in mods]
    if missing_targets:
        sys.exit("no such module: %s" % missing_targets)
    while todo:
        m = todo.pop()
        if m in closure:
            continue
        closure.add(m)
        todo.extend(i for i in mods[m]["imports"] if i in mods)
    deps = {m: [i for i in mods[m]["imports"] if i in mods] for m in closure}
    level, order, state = {}, [], {}
    for start in sorted(closure):
        if start in level:
            continue
        stack = [(start, iter(deps[start]))]
        state[start] = 1
        while stack:
            node, it = stack[-1]
            for i in it:
                if state.get(i) == 1:
                    sys.exit("import cycle through %s and %s" % (node, i))
                if i not in level:
                    state[i] = 1
                    stack.append((i, iter(deps[i])))
                    break
            else:
                level[node] = 1 + max((level[i] for i in deps[node]), default=0)
                order.append(node)
                state[node] = 2
                stack.pop()
    if args.max_level is not None:
        closure = {m for m in closure if level[m] <= args.max_level}
        order = [m for m in order if m in closure]

    def args_of(m):
        if args.lean_args is not None:
            a = args.lean_args.split()
        else:
            a = list(LEAN_ARGS)
            if m.startswith(FIELDS):
                a += FIELDS_ARGS
        if args.threads:
            a += ["-j", str(args.threads)]
        return a

    stamp = hashlib.sha1((version + mathlib_rev).encode()).hexdigest()
    trace = {}
    for m in order:  # imports come first in `order`
        h = hashlib.sha1()
        h.update(stamp.encode())
        h.update(mods[m]["hash"].encode())
        h.update(" ".join(args_of(m)).encode())
        for i in sorted(mods[m]["imports"]):
            h.update(trace[i].encode() if i in trace else i.encode())
        trace[m] = h.hexdigest()

    # what earlier runs did
    status_path = os.path.join(out, "status.jsonl")
    last = {}
    if os.path.exists(status_path):
        with open(status_path) as f:
            for line in f:
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                last[r["m"]] = r

    def olean(m):
        return os.path.join(lib, *m.split(".")) + ".olean"

    done_ok = {m for m in closure if m in last and last[m]["ok"] and last[m]["trace"] == trace[m] and os.path.exists(olean(m))}
    known_bad = {m for m in closure if m in last and not last[m]["ok"] and last[m]["trace"] == trace[m]}
    total_lines = sum(mods[m]["lines"] for m in closure)
    print("%d modules to build (%d lines); %d already built, %d failed before with the same inputs"
          % (len(closure), total_lines, len(done_ok), len(known_bad)), flush=True)
    by_level = Counter(level[m] for m in closure)
    print("levels: %d; modules at the first levels: %s" % (len(by_level), [by_level[k] for k in sorted(by_level)[:10]]), flush=True)
    if args.dry_run:
        return

    prefix = []
    if args.sandbox:
        readable = [os.path.expanduser("~/.elan"), os.path.join(ws, ".lake"), src, out]
        if overlay:
            readable.append(overlay)
        profile = os.path.join(out, "sandbox.sb")
        with open(profile, "w") as f:
            f.write(sandbox_profile(out, readable))
        prefix = ["/usr/bin/sandbox-exec", "-f", profile]

    users = defaultdict(list)
    for m in closure:
        for i in deps[m]:
            if i in closure:
                users[i].append(m)
    waiting = {m: sum(1 for i in deps[m] if i in closure and i not in done_ok) for m in closure if m not in done_ok}
    ready = deque(sorted((m for m, n in waiting.items() if n == 0 and m not in known_bad), key=lambda m: (level[m], m)))
    if args.shuffle is not None:
        import random
        pool = list(ready)
        random.Random(args.shuffle).shuffle(pool)
        ready = deque(pool)
    failed = set(known_bad)
    lock = threading.Lock()
    cond = threading.Condition(lock)
    counters = {"ok": 0, "fail": 0, "lines": 0, "running": 0, "started": 0, "cpu": 0.0}
    status = open(status_path, "a")
    compile_env = {"LEAN_PATH": lean_path, "PATH": "/usr/bin:/bin", "HOME": out, "LEAN_ABORT_ON_PANIC": "1"}
    stop = {"flag": False}

    def compile_one(m):
        target = olean(m)
        os.makedirs(os.path.dirname(target), exist_ok=True)
        cmd = prefix + [lean, "--root=" + src, "-o", target, "-i", target[:-6] + ".ilean"] + args_of(m) + [mods[m]["path"]]
        log = os.path.join(fail_dir, m + ".log")
        t = time.time()
        with open(log, "wb") as lf:
            p = subprocess.Popen(cmd, cwd=cwd, env=compile_env, stdout=lf, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
            timer = threading.Timer(args.timeout, p.kill)
            timer.start()
            try:
                _, rc, ru = os.wait4(p.pid, 0)
            finally:
                timer.cancel()
        p.returncode = rc
        secs = time.time() - t
        code = os.waitstatus_to_exitcode(rc)
        ok = code == 0 and os.path.exists(target)
        with open(log, "rb") as lf:
            text = lf.read().decode("utf-8", "replace")
        warnings = text.count(": warning:")
        if ok:
            os.remove(log)
        else:
            for stale in (target, target[:-6] + ".ilean"):
                if os.path.exists(stale):
                    os.remove(stale)
        first_error = ""
        if not ok:
            for line in text.split("\n"):
                if ": error" in line:
                    first_error = line[:300]
                    break
            if not first_error:
                first_error = "exit %d: %s" % (code, text.strip().split("\n")[-1][:200] if text.strip() else "no output")
        return {"m": m, "ok": ok, "s": round(secs, 2), "cpu": round(ru.ru_utime + ru.ru_stime, 2), "rss": ru.ru_maxrss,
                "rc": code, "warn": warnings, "trace": trace[m], "lines": mods[m]["lines"], "err": first_error}

    def worker():
        while True:
            with cond:
                while not ready and counters["running"] > 0 and not stop["flag"]:
                    cond.wait()
                if stop["flag"] or not ready:
                    cond.notify_all()
                    return
                if args.limit is not None and counters["started"] >= args.limit:
                    stop["flag"] = True
                    cond.notify_all()
                    return
                m = ready.popleft()
                counters["running"] += 1
                counters["started"] += 1
            r = compile_one(m)
            with cond:
                counters["running"] -= 1
                counters["cpu"] += r["cpu"]
                status.write(json.dumps(r) + "\n")
                status.flush()
                if r["ok"]:
                    counters["ok"] += 1
                    counters["lines"] += r["lines"]
                    for u in users[m]:
                        waiting[u] -= 1
                        if waiting[u] == 0 and u not in known_bad:
                            ready.append(u)
                else:
                    counters["fail"] += 1
                    failed.add(m)
                    print("FAILED %s (%.0f s): %s" % (m, r["s"], r["err"]), flush=True)
                cond.notify_all()

    start = time.time()
    threads = [threading.Thread(target=worker, daemon=True) for _ in range(args.jobs)]
    for t in threads:
        t.start()
    built_before = len(done_ok)
    lines_before = sum(mods[m]["lines"] for m in done_ok)
    try:
        while any(t.is_alive() for t in threads):
            time.sleep(60)
            with lock:
                el = time.time() - start
                rate = counters["lines"] / el if el else 0
                left = total_lines - lines_before - counters["lines"]
                print("[%5.0f min] built %d (+%d earlier), failed %d, running %d, ready %d; %.0f lines/s, %.1f CPU-s per module; "
                      "at this rate %.1f h for the rest" % (el / 60, counters["ok"], built_before, counters["fail"], counters["running"],
                                                          len(ready), rate, counters["cpu"] / max(1, counters["ok"] + counters["fail"]),
                                                          left / rate / 3600 if rate else float("inf")), flush=True)
    except KeyboardInterrupt:
        stop["flag"] = True
        with cond:
            cond.notify_all()
    for t in threads:
        t.join()
    status.close()

    # the summary: what failed, and how much each failure blocks
    blocked_by = {}
    for f in failed:
        seen, todo = set(), list(users[f])
        while todo:
            u = todo.pop()
            if u in seen:
                continue
            seen.add(u)
            todo.extend(users[u])
        blocked_by[f] = len(seen)
    ok_now = built_before + counters["ok"]
    print("\nbuilt %d of %d modules (%d in this run, %.0f min, %.1f CPU-h); %d failed"
          % (ok_now, len(closure), counters["ok"], (time.time() - start) / 60, counters["cpu"] / 3600, len(failed)))
    if failed:
        all_blocked = set()
        for f in failed:
            todo = list(users[f])
            while todo:
                u = todo.pop()
                if u not in all_blocked:
                    all_blocked.add(u)
                    todo.extend(users[u])
        print("%d modules cannot be built until the failures are fixed" % len(all_blocked - failed))
        errs = {}
        if os.path.exists(status_path):
            with open(status_path) as f:
                for line in f:
                    try:
                        r = json.loads(line)
                    except ValueError:
                        continue
                    errs[r["m"]] = r.get("err", "")
        for f in sorted(failed, key=lambda f: -blocked_by[f])[:40]:
            print("  blocks %6d  %s\n                 %s" % (blocked_by[f], f, errs.get(f, "")[:220]))


if __name__ == "__main__":
    main()
