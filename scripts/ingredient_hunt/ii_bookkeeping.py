#!/usr/bin/env python3
"""Ingredient II bookkeeping: what every-(q,a) statements known inputs give at x~q^{2.2}.

Honest ledger (no fabrication of unpublished exponents):
  - GRH => L=2+eps
  - FI sieve Linnik (arXiv:2303.06122): L huge (~7.5e7 in that write-up)
  - FI exceptional case: L=2-1/55 conditional on exceptional zero (older FI work)
  - Heath-Brown / Xylouris: L=5.5 / 5.18 via density+zero-free (uses zero info)
  - Bombieri-Vinogradov: average over q <= x^{1/2}/log^B — NOT every q~x^{1/2.2}
  - BDH: average over a — NOT every a
  - Maynard GPY: needs level of distribution averaged over moduli — not single AP Linnik
  - Chebotarev cyclotomic: disc ~ q^{phi(q)} kills exponents (Batch 7)
  - Linear-k barrier: defeated only by arithmetic forcing phases unaligned

Print comparison table of 'every-(q,a) at x=q^L?' for each class of input.
"""
from __future__ import annotations

rows = [
    ("zero-density + triangle (CGL A=7/3)", "yes (via Linnik deduction)", "2.2 formal / ~2.199 cert", "uses zero info"),
    ("signed Z every-a saving", "equiv. to PNT-in-AP", "circular", "barrier: triangle achievable"),
    ("GRH", "yes", "2+eps", "conditional"),
    ("FI sieve Linnik 2023", "yes", "~7.5e7 (their write-up)", "no density; useless for 2.2"),
    ("FI exceptional chi helps", "yes if Siegel zero", "2-1/55 (conditional)", "one chi; not sigma=5/7 box"),
    ("Heath-Brown / Xylouris", "yes", "5.5 / 5.18", "USES density+zero-free"),
    ("Bombieri-Vinogradov", "NO (avg over q)", "—", f"q up to x^{{1/2}}; need q~x^{{1/2.2}} pointwise"),
    ("BDH", "NO (avg over a)", "—", "L2 over a"),
    ("Maynard/GPY weights", "NO alone", "—", "needs averaged AP distribution"),
    ("Zhang/Polymath dispersion", "smooth moduli avg", "—", "not prime q every a"),
    ("Chebotarev Q(zeta_q)", "in principle", "disc kills", "Batch 7 Dead"),
    ("DFI Kloosterman bilinear", "partial ranges", "—", "not full Linnik every a at 2.2"),
    ("HB identity + Weil mod p", "Type I/II pieces", "—", "feeds sieves; not by itself Linnik@2.2"),
]


def main():
    print(f"{'input':<36} {'every-(q,a)?':<28} {'L or range':<28} {'note'}")
    print("-" * 120)
    for a, b, c, d in rows:
        print(f"{a:<36} {b:<28} {c:<28} {d}")
    print()
    print("Test at x~q^{2.2}: NO listed arithmetic input gives a new every-(q,a) prime")
    print("lower bound beyond what zero-density already gives, except FI's huge-L proof")
    print("(which avoids density but loses the exponent race).")


if __name__ == "__main__":
    main()
