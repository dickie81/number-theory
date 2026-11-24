#!/usr/bin/env python3
"""Write the copies of the archive's files in which `unfold … Matrix.mulVec …` is spelt as the file means it.

    python3 -I tools/rh/unfold_overlay.py [--function Matrix.mulVec] [--full-only] [--overlay DIR] [--dry-run]

`unfold f` rewrites with the lemma `f.eq_def` when the environment has one, and otherwise, for an `f` that is not
recursive, puts the body of `f` in its place. The two differ where `f` is not applied to all of its arguments
(`M *ᵥ fun a => …` unfolds in the second way and "fails to unfold" in the first). Lean makes `f.eq_def` only when
something asks for it, and keeps it in the compiled file of whoever asked. Four files of the archive name
`Matrix.mulVec.eq_def`, so a file that imports one of them has the lemma and a file that imports none has not; in
a bundle (`bundle_build.py`) every file above the first of the four has it.

So for each file that unfolds the function and sees none of the files that name its `eq_def` (itself included),
this writes a copy under the overlay tree, which `bundle_build.py` compiles in place of the archive's file, with
the list cut at the function: `unfold a Matrix.mulVec b` becomes `(unfold a; delta Matrix.mulVec; unfold b)`.
`delta` is what `unfold` does there when it has no lemma, so the copy says what the file says alone. The copy
has the lines of the original, one for one.

The function is taken by its last name too (`mulVec` under `open Matrix`), unless the file sees a declaration of
the archive with that last name: then the short name may be that one, and the line is left and reported.

It is for a function that is not recursive: for a recursive one `unfold` always uses the lemma.
"""
import argparse
import json
import os
import pickle
import re
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
NAME = r"[^\W\d][\w.'₀-₉!?]*"
END = re.compile(r";|<;>|\)|\]|\||$")

# lines left as the archive has them, though the rule above would cut them: there `delta` does not do what
# `unfold` does ("did not delta reduce [Finsupp.prod] at hp", on a hypothesis made by `have hp :=
# Finsupp.prod_mapDomain_index_inj …`), and the archive's `unfold` passes in the bundle. Found on 22 November
# 2026 by the kernel pass (`bundle_replay.py`): the error had gone unrecorded, and the two theorems were kept
# with `sorry`. (file, line)
LEAVE = {
    ("Formalism/LocalToGlobal/KernelLattices/KernelLocalFactors/InterlaceDifferenceShiftInvariant.lean", 4571),
    ("Formalism/LocalToGlobal/GlobalTheory/GL4/ColAddGenCastSuccRename.lean", 143),
}


def split_line(line, full, short_ok):
    """The line with each `unfold` list that names the function cut there; and how many were cut."""
    short = full.rsplit(".", 1)[-1]
    out, pos, cut = [], 0, 0
    for m in re.finditer(r"(?<![\w.'])unfold(?![\w.'])", line):
        if m.start() < pos:
            continue
        end = END.search(line, m.end()).start()
        seg = line[m.end():end]
        names, _, loc = seg.partition(" at ")
        words = names.split()
        if not words or not all(re.fullmatch(NAME, w) for w in words):
            continue
        hits = [k for k, w in enumerate(words) if w == full or (short_ok and w == short)]
        if not hits:
            continue
        loc = (" at " + loc.strip()) if loc.strip() else ""
        parts, run = [], []
        for k, w in enumerate(words):
            if k in hits:
                if run:
                    parts.append("unfold " + " ".join(run) + loc)
                    run = []
                parts.append("delta " + w + loc)
            else:
                run.append(w)
        if run:
            parts.append("unfold " + " ".join(run) + loc)
        tail = seg[len(seg.rstrip()):]
        out.append(line[pos:m.start()] + "(" + "; ".join(parts) + ")" + tail)
        pos = end
        cut += 1
    out.append(line[pos:])
    return "".join(out), cut


def main():
    ext = os.path.join(REPO, "external", "alpoge-rh")
    ap = argparse.ArgumentParser()
    ap.add_argument("--function", default="Matrix.mulVec")
    ap.add_argument("--src", default=os.path.join(ext, "extract", "lean", "src"))
    ap.add_argument("--scan", default=os.path.join(ext, "scan.json"))
    ap.add_argument("--map", default=os.path.join(ext, "declmap"))
    ap.add_argument("--overlay", default=os.path.join(ext, "overlay"))
    ap.add_argument("--full-only", action="store_true",
                    help="leave the short name alone (`prod` is not `Finsupp.prod` often enough)")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    full = args.function
    short = full.rsplit(".", 1)[-1]
    with open(args.scan) as f:
        mods = json.load(f)["modules"]
    with open(os.path.join(args.map, "graph.pkl"), "rb") as f:
        g = pickle.load(f)
    # the files of the archive that declare something with the function's last name
    homonyms = {g["files"][g["d_file"][d]][:-5].replace(os.sep, ".")
                for d, names in enumerate(g["names"]) for n in names if n == short or n.endswith("." + short)}
    asks = re.compile(r"(?<![\w'])(?:" + re.escape(full) + "|" + re.escape(short) + r")\.(?:eq_def|eq_unfold)(?![\w'])")
    uses = re.compile(r"(?<![\w.'])unfold(?![\w.'])[^\n]*(?<![\w'])" + re.escape(short) + r"(?![\w'.])")
    realizers, users = set(), []
    for m, rec in mods.items():
        path = os.path.join(args.src, m.replace(".", os.sep) + ".lean")
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
        if short not in text:
            continue
        if asks.search(text):
            realizers.add(m)
        if uses.search(text):
            users.append(m)
    print("%d files name %s.eq_def; %d files unfold %s" % (len(realizers), full, len(users), short))

    def closure(m):
        seen, stack = {m}, [m]
        while stack:
            for i in mods[stack.pop()]["imports"]:
                if i in mods and i not in seen:
                    seen.add(i)
                    stack.append(i)
        return seen

    written = lines_cut = with_lemma = 0
    left = defaultdict(list)
    for m in sorted(users, key=lambda m: (mods[m]["level"], m)):
        seen = closure(m)
        if seen & realizers:
            with_lemma += 1
            continue
        rel = m.replace(".", os.sep) + ".lean"
        over = os.path.join(args.overlay, rel)
        # a copy that is there already (a line repaired by hand) is the text to go on from
        with open(over if os.path.exists(over) else os.path.join(args.src, rel), encoding="utf-8",
                  errors="replace") as f:
            lines = f.read().split("\n")
        short_ok = not args.full_only and not (seen & homonyms)
        changed = 0
        for k, line in enumerate(lines):
            if "unfold" not in line or short not in line or (rel, k + 1) in LEAVE:
                continue
            new, cut = split_line(line, full, short_ok)
            if cut:
                lines[k] = new
                changed += cut
            elif uses.search(line) and not short_ok and re.search(r"(?<![\w.'])" + re.escape(short) + r"(?![\w'.])",
                                                                 line.split("unfold", 1)[1]):
                left[rel].append(k + 1)
        if changed:
            written += 1
            lines_cut += changed
            if not args.dry_run:
                os.makedirs(os.path.dirname(over), exist_ok=True)
                with open(over, "w", encoding="utf-8") as f:
                    f.write("\n".join(lines))
            print("  level %3d  %s: %d" % (mods[m]["level"], rel, changed))
    print("%d files import a file that names the lemma, and are left as they are; %d copies %s, %d lists cut"
          % (with_lemma, written, "would be written" if args.dry_run else "written", lines_cut))
    for rel, ks in sorted(left.items()):
        print("  left alone, the short name may be the archive's: %s lines %s" % (rel, ks))


if __name__ == "__main__":
    main()
