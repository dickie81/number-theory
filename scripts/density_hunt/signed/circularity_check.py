#!/usr/bin/env python3
"""Circularity: every-a saving on Z(a) is equivalent to a PNT-in-AP at the same x.

From the smoothed explicit formula (errors suppressed):
  phi(q) psi_f(x; q, a) = hat{f}(1) x - Z(a) + O(error).
So |Z(a)| <= q^{-theta} |Z|_triangle for ALL a
  <=>  psi_f(x; q, a) = x/phi(q) + O(q^{-theta} |Z|_triangle / phi(q))  for ALL a.

At x = q^L with L near 11/5 and |Z|_triangle ~ q^{A(1-sigma)} x^sigma, this is a
uniform prime-number theorem in APs at the Linnik scale — i.e. Linnik itself.
Proving the saving in order to deduce Linnik is circular unless the proof uses
information not equivalent to prime counts in the progression.

Inputs that can break circularity (not equivalent to psi(.;q,a) for this fixed q):
  - Bombieri-Vinogradov / Barban-Davenport-Halberstam (averages over q or a);
  - short intervals / Type I/II bilinear forms (the formalised sieve route);
  - Deuring-Heilbronn repulsion (exceptional zero arithmetic);
  - RMT heuristics for off-line zeros (not theorems).

Also records the Tao group mismatch: Z is Fourier on (Z/q)* ~= Z/(q-1), and for
prime q>3 the order q-1 is even, hence composite — Tao's strong p-group form
never applies on the character group.
"""
from __future__ import annotations

from fractions import Fraction as Fr

A = Fr(7, 3)
SIGMA = Fr(5, 7)
L = Fr(11, 5)


def main():
    exp = A * (1 - SIGMA) - L * (1 - SIGMA)
    print("Equivalence bookkeeping at sigma=5/7, A=7/3, x=q^L, L=11/5")
    print(f"  |Z|_triangle / x  ~  q^{{(A-L)(1-sigma)}} = q^{{{exp}}} = q^{float(exp):.6f}")
    print(f"  Triangle alone FAILS positivity by a factor q^{float(exp):.4f} (logs ignored).")
    print(f"  A saving of order q^{-0.038095} on |Z| restores the threshold;")
    print("  any extra theta>0 beats L=11/5.")
    print()
    print("Circularity verdict:")
    print("  every-a |Z| saving at this scale  ==  every-a PNT-in-AP at this scale")
    print("  ==  Linnik-type bound (same problem).")
    print("  Zero-density + triangle is the NON-circular classical route (counts, not signs).")
    print("  Signed saving needs arithmetic input beyond zero locations, or is circular.")
    print()
    print("Tao group mismatch:")
    print("  Z(a) is Fourier on (Z/q)* ~= Z/(q-1). For prime q>3, q-1 is even >2,")
    print("  hence COMPOSITE — Tao's |supp|+|supp hat|>=p+1 does NOT apply to this group.")
    print("  Donoho-Stark |supp|*|supp hat|>=q-1 still applies, and is saturated by")
    print("  subgroups — not an obstruction to ||Z||_inf = ||c||_1.")


if __name__ == "__main__":
    main()
