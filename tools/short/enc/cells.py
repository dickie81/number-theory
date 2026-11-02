#!/usr/bin/env python3
"""The certificate's root cells at θ = 21/40 as Lean modules, one per cell, and their assembly.

    python3 tools/short/enc/cells.py write ROOT SKELETON SOURCE   # the cell's module from a skeleton (Enc.lean skel)
    python3 tools/short/enc/cells.py assemble                     # lib/pnt/ShortSieve525.lean from the registry
    python3 tools/short/enc/cells.py check                        # the registry, the modules and the assembly agree
    python3 tools/short/enc/cells.py rewrite                      # every module again from its skeleton

The roots: `0 … 143` are region C's cells `(k, j) = (2 + i // 8, 2 + i % 8)`, `180 … 239` the cells outside it
`(10 + q // 6, 8 + q % 6)`, `q = i − 180`. The cell `(k, j)` of region C is the module `ShortSieve525Ckkjj`, outside it
`ShortSieve525Okkjj`; each holds `cert_cell` (`ShortSieveCertData`) on its skeleton, compressed (DEFLATE) and in base64,
and so the definitions `Ckkjj_0`, …, `Ckkjj` and the theorem `Ckkjj_run`. The registry `cells525.tsv` keeps a line per
cell: its loss (units `2^-50`), its cut points, the skeleton's size and where the certificate came from (`SOURCE`:
the generator's options, or the run). `write` replaces a cell only if its new loss is smaller, or with `--force`.
"""
import base64
import os
import re
import sys
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
LIB = os.path.join(ROOT, "lib", "pnt")
REG = os.path.join(HERE, "cells525.tsv")
FIELDS = ["root", "name", "loss", "cuts", "tokens", "bytes", "source"]
SC = 2 ** 50
# The patterns of scripts/check_hygiene.py, which scans the modules' text, the data included.
HYGIENE = re.compile(r"\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(?:private\s+|protected\s+)?axiom\s"
                     r"|\bimplemented_by\b|@\[extern\b|^\s*unsafe\s|\bofReduceBool\b|\bskipKernelTC\b|^#exit\b")
ROOTS = list(range(144)) + list(range(180, 240))


def cell(i):
    """The root's cell: (k, j, region C?, name)."""
    if i < 144:
        k, j, r = 2 + i // 8, 2 + i % 8, True
    else:
        k, j, r = 10 + (i - 180) // 6, 8 + (i - 180) % 6, False
    return k, j, r, f"{'C' if r else 'O'}{k:02d}{j:02d}"


def module(i):
    return "ShortSieve525" + cell(i)[3]


def registry():
    reg = {}
    if os.path.exists(REG):
        for line in open(REG, encoding="utf-8").read().splitlines()[1:]:
            p = line.split("\t")
            reg[int(p[0])] = dict(zip(FIELDS, p))
    return reg


def save(reg):
    with open(REG, "w", encoding="utf-8") as f:
        f.write("\t".join(FIELDS) + "\n")
        for i in sorted(reg):
            f.write("\t".join(str(reg[i][x]) for x in FIELDS) + "\n")


def header(text):
    """The skeleton's header: the loss and the cut points' losses."""
    t = text.split(None, 3)
    if len(t) < 3 or t[0] != "L":
        raise SystemExit("not a skeleton")
    total, n = int(t[1]), int(t[2])
    ls = [int(x) for x in t[3].split(None, n)[:n]] if n else []
    if sum(ls) != total:
        raise SystemExit("the cut points' losses do not add up")
    return total, ls


def blob(raw):
    """The skeleton compressed (raw DEFLATE) and in base64, as lines of 100 characters."""
    co = zlib.compressobj(9, zlib.DEFLATED, -15, 9)
    b = base64.b64encode(co.compress(raw) + co.flush()).decode()
    return [b[i:i + 100] for i in range(0, len(b), 100)]


def text_of(i, raw, total, ncut):
    k, j, r, name = cell(i)
    region = "region C" if r else "outside region C"
    lines = blob(raw)
    head = [
        "/-",
        f"# θ = 21/40: the certificate of the root cell `({k}, {j})`, {region}",
        "",
        f"The cell `({k}/40, {k + 1}/40] × [{j}/40, {j + 1}/40)` of `(α₁, α₂)`: `{name}_run` states that the checker",
        f"`ShortSieveCert.run` returns the loss `{total}` (units `2^-50`, `{total / SC:.6f}`) on the certificate",
        f"`{name}`, " + (f"whose {ncut} cut points (`{name}_0` …) are each" if ncut > 1
                         else f"whose cut point `{name}_0` is")
        + " checked by `decide +kernel` (`ShortSieveCertData`).",
        "Written by `tools/short/enc/cells.py` from the encoder's skeleton (`tools/short/enc`); do not edit by hand.",
        "-/",
        "import ShortSieveCertData",
        "",
        "namespace ShortSieve525",
        "",
        f'cert_cell {name} {k} {j} {"true" if r else "false"} "',
    ]
    return "\n".join(head + lines) + '"\n\nend ShortSieve525\n'


def write(args):
    force = "--force" in args
    args = [a for a in args if a != "--force"]
    i, skel, source = int(args[0]), args[1], " ".join(args[2:]) or "-"
    raw = open(skel, "rb").read()
    total, ls = header(raw.decode())
    reg = registry()
    if i in reg and int(reg[i]["loss"]) <= total and not force:
        print(f"root {i}: kept ({reg[i]['loss']} ≤ {total})")
        return 0
    text = text_of(i, raw, total, len(ls))
    bad = [x for x in text.splitlines() if HYGIENE.search(x)]
    if bad:
        raise SystemExit(f"root {i}: the data holds a pattern that check_hygiene.py rejects: {bad[0][:60]}")
    open(os.path.join(LIB, module(i) + ".lean"), "w", encoding="utf-8").write(text)
    reg[i] = {"root": i, "name": cell(i)[3], "loss": total, "cuts": len(ls), "tokens": len(raw.split()),
              "bytes": sum(len(x) for x in blob(raw)), "source": source}
    save(reg)
    print(f"root {i}: {module(i)} loss {total} ({total / SC:.6f}), {len(ls)} cut points")
    return 0


def assembly(reg):
    cs = [i for i in ROOTS if i < 144]
    os_ = [i for i in ROOTS if i >= 180]
    lossC = sum(int(reg[i]["loss"]) for i in cs)
    lossO = sum(int(reg[i]["loss"]) for i in os_)
    total = lossC + lossO

    def rows(items, per):
        return ",\n    ".join(", ".join(items[n:n + per]) for n in range(0, len(items), per))

    out = [
        "/-",
        "# θ = 21/40: the certificate's 204 root cells",
        "",
        "The certificates of the root cells, one module each (`ShortSieve525Ckkjj`, `ShortSieve525Okkjj`, written by",
        "`tools/short/enc/cells.py`), assembled by `ShortSieveCert.primes_of_certs`: for large `x` and",
        "`x^{21/40} ≤ y ≤ x^{1−ρ}`, `π(x) − π(x − y) ≥ (1 − L/2^50 − ε) y/log x` with",
        f"`L = {total}` (`{total / SC:.6f}`: region C `{lossC / SC:.6f}`, outside it `{lossO / SC:.6f}`), given Li's",
        "Lemmas 3.1, 3.2 and 4.1 (`ShortSieveCert.Hyps`). The bound is positive when `L < 2^50`.",
        "",
        "The file imports the 204 cell modules.",
        "-/",
    ]
    out += [f"import {module(i)}" for i in ROOTS]
    out += [
        "",
        "/-! The certificates of the root cells, their losses (units `2^-50`), and the lower bound for primes. -/",
        "",
        "namespace ShortSieve525",
        "",
        "open ShortSieveCert Finset Filter",
        "",
        "/-- The certificates of region C's cells `(k, j)`, `2 ≤ k ≤ 19`, `2 ≤ j ≤ 9`, in the order of `(k, j)`. -/",
        "noncomputable def certsC : List Cert := [",
        "    " + rows([cell(i)[3] for i in cs], 10) + "]",
        "",
        "/-- The certificates of the cells `(k, j)` outside region C, `10 ≤ k ≤ 19`, `8 ≤ j ≤ 13`. -/",
        "noncomputable def certsO : List Cert := [",
        "    " + rows([cell(i)[3] for i in os_], 10) + "]",
        "",
        "/-- The losses of region C's cells. -/",
        "def lossesC : List ℕ := [",
        "    " + rows([str(reg[i]["loss"]) for i in cs], 6) + "]",
        "",
        "/-- The losses of the cells outside region C. -/",
        "def lossesO : List ℕ := [",
        "    " + rows([str(reg[i]["loss"]) for i in os_], 6) + "]",
        "",
        "/-- The certificate of a root cell. -/",
        "noncomputable def cert (r : Bool) (c : ℕ × ℕ) : Cert :=",
        "  if r then certsC.getD ((c.1 - 2) * 8 + (c.2 - 2)) .out else certsO.getD ((c.1 - 10) * 6 + (c.2 - 8)) .out",
        "",
        "/-- The loss of a root cell. -/",
        "def loss (r : Bool) (c : ℕ × ℕ) : ℕ :=",
        "  if r then lossesC.getD ((c.1 - 2) * 8 + (c.2 - 2)) 0 else lossesO.getD ((c.1 - 10) * 6 + (c.2 - 8)) 0",
        "",
        "theorem run_cert : ∀ r, ∀ c ∈ ShortSieveThree.cells r,",
        "    run 1 (cert r c) (.std 1) (cellCons c.1 r) (cellBox c.1 c.2) true = some (loss r c) := by",
        "  rintro (_ | _) ⟨k, j⟩ hc <;>",
        "    simp only [ShortSieveThree.cells, Bool.false_eq_true, ↓reduceIte, mem_product, mem_Icc] at hc <;>",
        "    obtain ⟨⟨hk₁, hk₂⟩, hj₁, hj₂⟩ := hc <;> interval_cases k <;> interval_cases j",
        "  exacts [",
        "    " + rows([cell(i)[3] + "_run" for i in os_ + cs], 8) + "]",
        "",
        "theorem loss_sum : ∑ c ∈ ShortSieveThree.cells true, loss true c + "
        "∑ c ∈ ShortSieveThree.cells false, loss false c =",
        f"    {total} := by",
        "  decide +kernel",
        "",
        "/-- **The lower bound for primes in short intervals at `θ = 21/40` from the certificate.** With Li's",
        "Lemmas 3.1, 3.2 and 4.1 (`Hyps`), `π(x) − π(x − y) ≥ (1 − L/2^50 − ε) y/log x` for large `x` and",
        f"`x^{{21/40}} ≤ y ≤ x^{{1−ρ}}`, with the certificate's loss `L = {total}`. -/",
        "theorem primes_525 {ρ c : ℝ} (H : Hyps ρ c) :",
        "    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ^ (21 / 40 : ℝ) ≤ y → y ≤ x ^ (1 - ρ) →",
        f"      (1 - ({total} : ℝ) / SC - ε) * y / Real.log x ≤ ((Ioc ⌊x - y⌋₊ ⌊x⌋₊).filter Nat.Prime).card := by",
        "  have h : ∑ c ∈ ShortSieveThree.cells true, (loss true c : ℝ) / SC +",
        f"      ∑ c ∈ ShortSieveThree.cells false, (loss false c : ℝ) / SC = ({total} : ℝ) / SC := by",
        "    rw [← sum_div, ← sum_div, ← add_div]",
        "    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ) / SC) loss_sum",
        "  simpa only [h] using primes_of_certs H one_pos cert loss run_cert",
        "",
        "end ShortSieve525",
        "",
    ]
    return "\n".join(out)


def assemble(_args):
    reg = registry()
    missing = [i for i in ROOTS if i not in reg]
    if missing:
        raise SystemExit(f"cells without a certificate: {missing}")
    open(os.path.join(LIB, "ShortSieve525.lean"), "w", encoding="utf-8").write(assembly(reg))
    total = sum(int(reg[i]["loss"]) for i in ROOTS)
    print(f"wrote lib/pnt/ShortSieve525.lean: L = {total} ({total / SC:.6f})")
    return 0


def data(i):
    """The skeleton held by a cell's module."""
    src = open(os.path.join(LIB, module(i) + ".lean"), encoding="utf-8").read()
    m = re.search(r'cert_cell \S+ \d+ \d+ \S+ "\n(.*?)"', src, re.S)
    return src, (zlib.decompress(base64.b64decode("".join(m.group(1).split())), -15) if m else b"")


def rewrite(_args):
    """Every cell's module written again from its own skeleton (after a change of the modules' form)."""
    for i in sorted(registry()):
        _, raw = data(i)
        total, ls = header(raw.decode())
        open(os.path.join(LIB, module(i) + ".lean"), "w", encoding="utf-8").write(text_of(i, raw, total, len(ls)))
    return 0


def check(_args):
    reg, bad = registry(), []
    for i in ROOTS:
        p = os.path.join(LIB, module(i) + ".lean")
        if i not in reg or not os.path.exists(p):
            bad.append(f"root {i}: {'no registry line' if i not in reg else 'no module'}")
            continue
        src, raw = data(i)
        try:
            total, ls = header(raw.decode())
        except SystemExit as e:
            bad.append(f"root {i}: {e}")
            continue
        if src != text_of(i, raw, total, len(ls)) or int(reg[i]["loss"]) != total:
            bad.append(f"root {i}: the module or the registry differs from what write gives")
    for f in os.listdir(LIB):
        m = re.fullmatch(r"ShortSieve525([CO]\d{4})\.lean", f)
        if m and m.group(1) not in {cell(i)[3] for i in ROOTS}:
            bad.append(f"{f}: not a root cell")
    asm = os.path.join(LIB, "ShortSieve525.lean")
    if not bad and (not os.path.exists(asm) or open(asm, encoding="utf-8").read() != assembly(reg)):
        bad.append("lib/pnt/ShortSieve525.lean differs from what assemble gives")
    for b in bad:
        print(b)
    print(f"CELLS {'PASS' if not bad else 'FAIL'} ({len(reg)} cells in the registry)")
    return 0 if not bad else 1


def main():
    cmds = {"write": write, "assemble": assemble, "check": check, "rewrite": rewrite}
    if len(sys.argv) < 2 or sys.argv[1] not in cmds:
        print(__doc__)
        return 2
    return cmds[sys.argv[1]](sys.argv[2:])


if __name__ == "__main__":
    sys.exit(main())
