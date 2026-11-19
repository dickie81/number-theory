#!/usr/bin/env python3
"""How the theorems of a census reach `Classical.choice`.

    python3 choice_kinds.py CENSUS.tsv EDGES LABELS_BINARY

Three kinds of use are told apart by where a chain of uses from the theorem first meets one of these constants:

* excluded middle: a theorem of the namespace `Classical` whose statement is free of choice (`Classical.em`,
  `Classical.byContradiction`, `Classical.not_not`, …), other than the forms of the axiom of choice
  (`Classical.axiomOfChoice`, `Classical.skolem`, `Classical.nonempty_pi`);
* classical decidability: `Classical.propDecidable`, an instance of `Decidable p` for every proposition `p`;
* choice of an element: any other route to `Classical.choice` (`Classical.choose`, `Nonempty.some`, …).

The chains are not followed below those constants. LABELS_BINARY is the compiled labels.c.
"""
import subprocess, sys
from collections import Counter
from census_report import load, written

LEM, DEC, CHOICE = 1, 2, 4
AC = {"Classical.axiomOfChoice", "Classical.axiom_of_choice", "Classical.skolem", "Classical.nonempty_pi"}

def main():
    tsv, edges, binary = sys.argv[1:4]
    ax, rows = load(tsv)
    ch = 1 << {v: k for k, v in ax.items()}["Classical.choice"]
    lem = {r[0] for r in rows if r[1] == "theorem" and r[0].startswith("Classical.") and r[0] not in AC
           and not (r[4] & ch) and (r[3] & ch)}
    lines = []
    for r in rows:
        if r[0] in lem: lines.append(f"{LEM} 1")
        elif r[0] == "Classical.propDecidable": lines.append(f"{DEC} 1")
        elif r[0] == "Classical.choice": lines.append(f"{CHOICE} 1")
        else: lines.append("0 0")
    labels = edges + ".labels"
    open(labels, "w").write("\n".join(lines) + "\n")
    masks = list(map(int, subprocess.run([binary, edges, str(len(rows)), labels], capture_output=True, text=True, check=True).stdout.split()))
    name = lambda m: " + ".join(n for b, n in ((LEM, "excluded middle"), (DEC, "classical decidability"), (CHOICE, "choice of an element")) if m & b)
    tainted = [(r, masks[i]) for i, r in enumerate(rows) if written(r) and (r[3] & ch)]
    for label, sel in (("theorems that depend on Classical.choice", tainted),
                       ("of them, those whose statement is free of choice", [(r, m) for r, m in tainted if not (r[4] & ch)])):
        print(f"{label}: {len(sel)}")
        for m, v in Counter(m for _, m in sel).most_common():
            print(f"  {v:7d}  {100 * v / len(sel):5.1f}%  {name(m)}")
        no_element = sum(1 for _, m in sel if not (m & CHOICE))
        print(f"  never by choice of an element: {no_element} ({100 * no_element / len(sel):.1f}%)")

if __name__ == "__main__":
    main()
