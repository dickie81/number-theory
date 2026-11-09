"""Sec. 11: what the Kuznetsov bound of Deshouillers-Iwaniec (Theorem 12, in Drappeau's form, Theorem 2.1, with the
Bombieri-Friedlander-Iwaniec correction D^2 N R) gives for the error F of Sec. 10.  Exponents of q, constants dropped.

The phase e(l k q Abar/B), A = a2 a3, B = b2 b3, forces: modulus s c = b2 b3 (c = b3 smooth), inverse r d = a2 a3
(d = a3 smooth), numerator n with coefficients b_{n,r,s}.  Two placements of the prime q:
  (i)  n = l k q, sparse multiples of q in a range of size x^4;
  (ii) n = l k, with q moved into the inverse, r = q a2 (size q x).
Bound: |sum| << K_DI ||b||_2, K_DI^2 = C S (R S + N)(C + R D) + C^2 D S ((R S + N) R)^(1/2) + D^2 N R."""
from fractions import Fraction as Fr

def kdi(C, D, N, R, S):        # exponent of K_DI (max of the three terms, halved)
    t1 = C + S + max(R + S, N) + max(C, R + D)
    t2 = 2*C + D + S + (max(R + S, N) + R)/2
    t3 = 2*D + N + R
    return max(t1, t2, t3)/2

for th in [Fr(7, 18), Fr(4, 9), Fr(1, 2)]:
    x = th; K = 3*th - 1                    # q^x, q^K with K = x^3/q
    triv = K + 4*x                          # trivial bound K x^4
    need = K + 3*x                          # what (H) needs, K x^3 q^-eta
    b2 = (2*x + (K - x)) / 2                # ||b||_2 = (x^2 * K/x)^(1/2): r, s in I, ||nu||_2^2 = K/x
    i = kdi(x, x, 4*x, x, x) + b2           # (i): N = x^4
    ii = kdi(x, x, x + K, 1 + x, x) + b2    # (ii): N = x K, R = q x
    print(f"x = q^{th}: trivial {float(triv):.3f}, needed < {float(need):.3f};  DI (i) {float(i):.3f} "
          f"(trivial + {float(i - triv):.3f}), DI (ii) {float(ii):.3f} (trivial + {float(ii - triv):.3f})")
