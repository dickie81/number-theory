#!/usr/bin/env python3
"""Check docs/account.md against the sources (no build needed).

    python3 scripts/check_account.py

The page is written by hand, so this keeps it from naming what the library no longer has. Every span in backticks that
reads as a dotted Lean name, such as `Eis.LFunction_ne_zero_of_re_gt`, must be the full name of a declaration of
lib/core, lib/pnt, lib/dh, lib/zeta23 or lib/check, as scripts/inventory.py reads them, or one of Lean's axioms. A span
that names a module file (`KubotaThetaProof.lean`) or a path under one of the repository's directories must exist, and
so must the target of every relative link.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_cone  # noqa: E402
import inventory  # noqa: E402

ROOT = import_cone.ROOT
PAGE = os.path.join(ROOT, "docs", "account.md")
TOP = {"lib", "docs", "formalisations", "papers", "scripts", "site", "tools", ".github"}
AXIOMS = {"Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][\w'!?]*(?:\.[\w'!?]+)+")
FILE = re.compile(r"\.(md|py|json|jsonl|tex|yml|html|cpp|sh)$")


def main():
    text = open(PAGE, encoding="utf-8").read()
    mods, _ = import_cone.sources()
    names = {full for p in mods.values() for full, *_ in inventory.declarations(os.path.join(ROOT, p))}
    leans = {f for _, _, fs in os.walk(os.path.join(ROOT, "lib")) for f in fs if f.endswith(".lean")}
    bad, checked = [], 0
    for span in re.findall(r"`([^`\n]+)`", text):
        span = span.replace("\\|", "|")
        if " " not in span and span.split("/")[0] in TOP:
            checked += 1
            if not os.path.exists(os.path.join(ROOT, span)):
                bad.append(f"no such path: {span}")
        elif re.fullmatch(r"\w+\.lean", span):
            checked += 1
            if span not in leans:
                bad.append(f"no such module: {span}")
        elif NAME.fullmatch(span) and not FILE.search(span):
            checked += 1
            if span not in names and span not in AXIOMS:
                bad.append(f"no such declaration: {span}")
    for target in re.findall(r"\]\(([^)\s]+)\)", text):
        if re.match(r"[a-z]+:", target):
            continue
        checked += 1
        if not os.path.exists(os.path.normpath(os.path.join(os.path.dirname(PAGE), target.split("#")[0]))):
            bad.append(f"broken link: {target}")
    for b in bad:
        print(b)
    print(f"{checked} names, paths and links checked; {len(bad)} missing")
    print("ACCOUNT", "PASS" if not bad else "FAIL")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
