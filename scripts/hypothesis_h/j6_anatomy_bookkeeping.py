"""Anatomy of J6 and Kl3/Deligne level-of-distribution bookkeeping at theta=7/18.

New angle vs cgl-s3 §9 exclusion (shifted d3 / D+S+F / Bettin-Chandee / Kuznetsov):
frame as level of distribution for the *restricted* ternary divisor r3^I
(three factors each in a dyadic interval of length x) in APs mod q.
Need: modulus q at X=x^3=q^{7/6}, i.e. level 6/7.
"""
THETA = 7 / 18


def main():
    print("=== sizes (x=q^theta, theta=7/18) ===")
    print(f"x = q^{THETA}")
    print(f"X = x^3 = q^{3*THETA} = q^{7/6}")
    print(f"K = floor(8x^3/q) ~ q^{3*THETA - 1} = q^{1/6}")
    print(f"|I|^6/q = q^{6*THETA - 1} = q^{4/3}   (main term scale)")
    print("error needed O(x^6 q^{-1-eta}) = q^{4/3 - eta}")
    print(
        f"diagonal N(0) ~ x^3 (log x)^c = q^{7/6} (log)^c; "
        f"ratio to main q^{7/6 - 4/3} = q^{{-1/6}} (power below main)"
    )

    print("\n=== J6 split ===")
    print("J6 = sum_{|k|<=K} N(kq),  N(h) = sum_m r3(m) r3(m+h)")
    print("  k=0: integer equality n1n2n3 = m1m2m3  (diagonal)")
    print("  0<|k|<=K: small multiples, h=kq ~ X")
    print("  Main term |I|^6/(q-1) arises as the singular-series average of N over k,")
    print("  equivalently as equidistribution of products among q residue classes:")
    print("    #products = |I|^3, each class ~ |I|^3/q, J6 ~ q*(|I|^3/q)^2 = |I|^6/q.")

    print("\n=== Level of distribution needed ===")
    print(f"theta_LoD = log(q)/log(X) = 1/(7/6) = 6/7 ≈ {6/7:.6f}")
    print("Literature for unrestricted d3 (NOT our short-interval r3^I):")
    print(f"  Friedlander–Iwaniec: 1/2+1/230 ≈ {0.5+1/230:.6f}")
    print(f"  Heath-Brown:         1/2+1/82  ≈ {0.5+1/82:.6f}")
    print(f"  FKM (prime moduli):  1/2+1/46  ≈ {0.5+1/46:.6f}")
    print(f"  FKM avg residue:     1/2+1/34  ≈ {0.5+1/34:.6f}")
    print(f"All << 6/7 (shortfall vs best prime: {6/7 - (0.5+1/46):.4f}).")

    print("\n=== Additive sum S(r) = sum_{n1,n2,n3 in I} e(r n1 n2 n3 / q) ===")
    print("Incomplete geometric (sum n3 first):")
    print("  |S(r)| << sum_{n1,n2} min(x, 1/||r n1 n2/q||) <<_eps x^3/q + x^2")
    print(f"  = q^{3*THETA-1} + q^{2*THETA} = q^{1/6} + q^{7/9}; dominant q^{7/9}")
    print("Parseval: sum_a E_a^2 = (1/q) sum_{r!=0} |S(r)|^2")
    print(f"  with |S|<<q^{7/9}: sum E^2 << q^{14/9} ≈ q^{1.556}")
    print(f"  need << q^{4/3}≈q^{1.333}; SHORT by q^{2/9}")
    print("Level reachable with |S|<<Y^2 alone: Q <= Y^2 = X^{2/3}, level <= 2/3 < 6/7.")
    print(f"To reach level 6/7 need RMS |S| << q^{2/3}; have pointwise << q^{7/9};")
    print(f"extra saving needed in S(r): q^{7/9 - 2/3} = q^{1/9}.")

    print("\n=== Deligne / hyper-Kloosterman after Poisson ===")
    print(f"Dual length M = q/x = q^{1-THETA} = q^{11/18}")
    print("Normalized Kl_3(a;q) := q^{-1} sum_{xyz=a} e((x+y+z)/q) satisfies |Kl_3| <= 2 (Deligne).")
    print("Unnormalized sum_{xyz=a} e(...) << q.")
    print("Crude: insert |Kl|<<q for all M^3 dual frequencies:")
    print("  |S| << (x/q)^3 * M^3 * q = q   (WORSE than incomplete geometric q^{7/9}).")
    print("Random-model dual (unproved): |S| << x^{3/2}/q^{1/2} = q^{1/12} — would give (H) amply.")
    print("Published FI/HB/FKM use Deligne on *auxiliary* FI-sums / Kl correlations to break")
    print("1/2, reaching only ~1/2+1/46 for unrestricted d3 — still far from 6/7.")
    print("Short dyadic factors do NOT automatically upgrade LoD to 6/7: the incomplete")
    print("geometric bound is the natural exploitation of |I|=x short, and it only reaches 2/3.")

    print("\n=== Average over k (the q^{1/6} shifts) ===")
    print("Averaging over k=1..K of N(kq) is exactly sum_a r3^I(a)^2 = J6.")
    print("Dense-interval averages of shifted d3 (MRT, Baier–Browning–... ) need h running")
    print("over an interval; our shifts are K points spaced q apart (spacing X^{6/7}).")
    print("That sparse average is NOT supplied by the known averaged shifted-d3 theorems")
    print("(already noted in cgl-s3 §9). Framing as LoD does not remove the sparsity.")

    print("\n=== Verdict on this angle ===")
    print("DEAD as a proof of (H): need LoD 6/7, best d3 technology ~1/2+1/46,")
    print("short-interval structure alone gives level <=2/3 via geometric sums,")
    print("still short of 6/7 by 6/7-2/3=4/21; Deligne Kl3 does not close the gap")
    print("without an unproved square-root cancellation over the dual frequencies.")


if __name__ == "__main__":
    main()
