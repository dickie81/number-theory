#!/usr/bin/env python3
"""The warnings check: a Lean build emits no warning in the library's own sources.

    python3 scripts/check_warnings.py BUILD_LOG      # the output of scripts/build.sh, lake build or lake env lean

Lake replays the messages of every module that it does not rebuild ("Replayed …"). So the log of a build lists every
warning of every module in the build, cached or not, and CI checks the whole library at every run without rebuilding it.

**What counts.** A warning counts when it is located (`file:line:col`) in a source of lib/core, lib/pnt, lib/dh,
lib/zeta23 or lib/check.

**What does not count:**
- warnings in the vendored libraries (lib/vendor), which must stay upstream's sources plus the port patches
  (scripts/check_vendor.py);
- Lake's note, once per module, that a file importing Mathlib is not itself a module of Lean's module system. That note
  carries no line, and clearing it means moving the library to the module system, a separate change.

The check prints each warning that counts, as a GitHub annotation when it runs in Actions, and fails if there is one.
"""
import os
import re
import sys

OWN = ("lib/core/", "lib/pnt/", "lib/dh/", "lib/zeta23/", "lib/check/")
STAMP = re.compile(r"^\d{4}-\d\d-\d\dT[\d:.]+Z ")  # the timestamp that Actions puts on each line of a job's log
# Lake prints `warning: FILE:LINE:COL: MESSAGE`; lean alone (`lake env lean FILE`) prints `FILE:LINE:COL: warning: MESSAGE`
WARN = re.compile(r"^warning: (\S+?\.lean):(\d+):(\d+): (.*)$|^(\S+?\.lean):(\d+):(\d+): warning: (.*)$")


def warnings(path):
    """The warnings of the library's own sources in a build log, once each, in order."""
    out = {}
    for raw in open(path, encoding="utf-8", errors="replace"):
        m = WARN.match(STAMP.sub("", raw.rstrip("\n")))
        if not m:
            continue
        g = m.groups()
        src, line, col, msg = g[:4] if g[0] else g[4:]
        src = src.removeprefix("./")
        if src.startswith(OWN):
            out.setdefault((src, int(line), int(col), msg), None)
    return list(out)


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    found = warnings(sys.argv[1])
    actions = os.environ.get("GITHUB_ACTIONS") == "true"
    for src, line, col, msg in found:
        print(f"::error file={src},line={line},col={col}::{msg}" if actions else f"{src}:{line}:{col}: {msg}")
    files = len({w[0] for w in found})
    print(f"check_warnings: {len(found)} warnings in {files} files of the library's sources")
    print("WARNINGS PASS" if not found else "WARNINGS FAIL")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
