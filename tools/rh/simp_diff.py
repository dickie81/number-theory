#!/usr/bin/env python3
"""Say how the simp set of one version of Mathlib differs from another's, as far as it can be undone.

    python3 -I tools/rh/simp_diff.py OLD_SIMP.tsv NEW_SIMP.tsv OLD_NAMES.tsv NEW_NAMES.tsv
        [--lean OUT.lean] [--erase OUT.json]

The two SIMP lists are written by `lean/DumpSimp.lean` (`name`, used after or before the subterms, used from right
to left), the two NAMES lists by `lean/DumpNames.lean`. A proof written for the newer version calls `simp` with the
newer simp set. On the older version two differences can be undone without touching the proof:

* a lemma that both versions have and only the newer one marks `@[simp]`: OUT.lean gets `attribute [simp]` lines
  for those, to put in a file that the port imports (71 of them between Mathlib of 21 August and of 29 September
  2026, `Circle.norm_coe` among them);
* a lemma that both versions have and only the older one marks: OUT.json lists those, for `bundle_files.py
  --simp-out`, which takes them out of the simp set of every file it compiles (342; Lean's `Bool.cond_…` lemmas,
  the `coe_coe` lemmas of the homomorphism classes).

What cannot be undone this way: the lemmas that only the newer version has (2 827 simp lemmas), and the lemmas of
the older version that the newer one renamed or dropped, which stay.
"""
import argparse
import json


def simp_set(path):
    with open(path, encoding="utf-8") as f:
        return {tuple(line.rstrip("\n").split("\t")) for line in f if line.strip()}


def names(path):
    with open(path, encoding="utf-8") as f:
        return {line.split("\t", 1)[0] for line in f}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old_simp")
    ap.add_argument("new_simp")
    ap.add_argument("old_names")
    ap.add_argument("new_names")
    ap.add_argument("--lean")
    ap.add_argument("--erase")
    args = ap.parse_args()
    old, new = simp_set(args.old_simp), simp_set(args.new_simp)
    in_old, in_new = names(args.old_names), names(args.new_names)
    add = sorted(x for x in new - old if x[0] in in_old)
    out = sorted(x for x in old - new if x[0] in in_new)
    print("in both simp sets: %d; in the newer only: %d, of which the older version has the lemma: %d; "
          "in the older only: %d, of which the newer version has the lemma: %d"
          % (len(old & new), len(new - old), len(add), len(old - new), len(out)))
    if args.lean:
        with open(args.lean, "w", encoding="utf-8") as f:
            for name, post, inv in add:
                # after the subterms and from left to right is `simp`; before is `simp↓`; right to left `simp ←`
                attr = "simp" + ("" if post == "1" else "↓") + (" ←" if inv == "1" else "")
                f.write("attribute [%s] %s\n" % (attr, name))
    if args.erase:
        with open(args.erase, "w", encoding="utf-8") as f:
            json.dump([list(x) for x in out], f, ensure_ascii=False)


if __name__ == "__main__":
    main()
