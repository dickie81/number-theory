"""Moment / Burgess / dual bookkeeping for hypothesis (H) at x=q^{7/18}, V=x^{5/7}.

Does not prove (H). Prints exponents only.
"""
from math import log

THETA = 7 / 18
SIG = 5 / 7
VEXP = THETA * SIG  # 5/18


def mvt_count_exp(k: int) -> tuple[float, float, float]:
    """|W| << q^{e1} + q^{e2} from Σ|S|^{2k} << (q+x^k) x^k (log)^C, V=x^σ."""
    e1 = 1 - k / 6  # q * x^{k(1-2σ)} = q * q^{-k/6}
    e2 = 2 * k / 9  # x^k * x^{k(1-2σ)} = q^{2k/9}
    return e1, e2, max(e1, e2)


def burgess_B(r: int) -> float:
    """Classical Burgess: |S| << N^{1-1/r} q^{(r+1)/(4r^2)+ε}."""
    return (1 - 1 / r) * THETA + (r + 1) / (4 * r * r)


def dual_pv_exp() -> float:
    """Complete S_{[1,x]} via Gauss sums → dual length q/x = q^{11/18}; PV on dual."""
    # |S| << sqrt(q) log for any incomplete; dual short sum of length q/x
    # Completing: S(χ) = (τ(χ)/q) Σ_m χ̄(m) (e(-m a/q)-...)/ (1-e) roughly
    # Pointwise dual: |S_I| << sqrt(q) log always (PV) — weaker than V? PV exp=1/2 > Vexp
    return 0.5


def main():
    print(f"theta={THETA} sig={SIG} V~q^{VEXP}  target beat q^{2/3}")
    print("\n=== High moments (Montgomery-style MVT) ===")
    print(f"{'k':>3} {'q-term':>10} {'x^k-term':>10} {'|W|<<':>10} {'vs 2/3':>10}")
    for k in range(1, 9):
        e1, e2, mx = mvt_count_exp(k)
        print(f"{k:3d} {e1:10.4f} {e2:10.4f} {mx:10.4f} {'BEAT' if mx < 2/3 - 1e-12 else 'no':>10}")
    print("Optimal among this family: k=2 and k=3 both give exactly 2/3 at theta=7/18.")
    print("No k beats 2/3 without a saving in the congruence count J_{2k}.")

    print("\n=== Burgess individual (Form B, classical) vs V ===")
    for r in range(2, 9):
        b = burgess_B(r)
        print(f"r={r}: Burgess~q^{b:.4f}  V~q^{VEXP:.4f}  kills all chi? {b < VEXP}")
    print("Conclusion: Burgess does not put every |S|<V; no |W|=0 from individual bounds.")

    print("\n=== Dual / completing at theta=7/18 ===")
    print(f"dual length q/x = q^{1-THETA:.4f} = q^{11/18:.4f} > sqrt(q); still PV regime.")
    print(f"PV |S|<<q^{dual_pv_exp()} log > V~q^{VEXP}; does not forbid critical LV.")

    print("\n=== (H) price (from cgl-s3 §8, not re-derived) ===")
    print("If J6 = |I|^6/(q-1) + O(x^6 q^{-1-eta}), then A <= 7/3 - eta/2 + O(eta^2).")
    for eta in [0, 0.01, 0.02, 0.05, 0.1, 1 / 6, 5 / 18]:
        A = 7 / 3 - eta / 2
        print(f"  eta={eta:.4f}: A~={A:.5f}, sieve floor 1+A/2={1+A/2:.5f}")


if __name__ == "__main__":
    main()
