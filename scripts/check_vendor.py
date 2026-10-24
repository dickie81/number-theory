#!/usr/bin/env python3
"""Check that lib/vendor holds the upstream files at the pinned commits with the port patches applied.

For each vendored library: fetch the pinned commit of its upstream repository (network access needed), take every
`.lean` file present under lib/vendor/<name>/ and the license files from that commit, apply the library's port
patch with `patch -p1` in a temporary directory, and compare the result with lib/vendor/<name>/ byte for byte. A
vendored `.lean` file that is not in the upstream commit, a file that differs, or a patch that does not apply fails
the check.
"""
import filecmp
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VENDOR = [
    # name, upstream, commit, the upstream directory that lib/vendor/<name>/ mirrors, license files, patch
    ("pnt-plus", "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd",
     "650d31264be65f4cd6e70c45d8b25d86d482a761", "", ["LICENSE"], "pnt_port.patch"),
    ("zeta23", "https://github.com/anthropics/formal-math",
     "fbdc36bbf17d20af3fd0447c6d1a8a02773c9844", "zeta23/", ["LICENSE", "NOTICE"], "zeta23_port.patch"),
]


def sh(args, cwd, **kw):
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True, **kw).stdout


def check(name, url, rev, sub, licenses, patch, tmp):
    here = os.path.join(ROOT, "lib", "vendor", name)
    lean = sorted(os.path.relpath(os.path.join(d, f), here)
                  for d, _, fs in os.walk(here) for f in fs if f.endswith(".lean"))
    git = os.path.join(tmp, "git-" + name)
    os.makedirs(git)
    sh(["git", "init", "-q"], git)
    sh(["git", "fetch", "-q", "--depth", "1", url, rev], git)
    out = os.path.join(tmp, name)
    for rel in lean + licenses:
        dst = os.path.join(out, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, "wb") as fh:
            fh.write(sh(["git", "show", f"{rev}:{sub}{rel}"], git))
    sh(["patch", "-s", "-p1", "-i", os.path.join(here, patch)], out)
    bad = [rel for rel in lean + licenses
           if not filecmp.cmp(os.path.join(out, rel), os.path.join(here, rel), shallow=False)]
    print(f"{name}: {len(lean)} .lean files and {len(licenses)} license files at {rev[:7]}, patched with {patch}: "
          f"{len(lean) + len(licenses) - len(bad)} identical, {len(bad)} differ")
    for rel in bad:
        print("  DIFFERS:", rel)
    return not bad


def main():
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for v in VENDOR:
            try:
                ok &= check(*v, tmp)
            except subprocess.CalledProcessError as e:
                print(f"{v[0]}: {' '.join(e.cmd)} failed: {e.stderr.decode(errors='replace').strip()}")
                ok = False
    print("VENDOR", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
