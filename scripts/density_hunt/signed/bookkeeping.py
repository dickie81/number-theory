#!/usr/bin/env python3
"""Signed Z(a) bookkeeping for Linnik at the CGL corner.

Defines the smoothed signed quantity matching the classical explicit formula,
compares triangle (density) vs target savings for L < 11/5, 2.198, 2.167,
and records the sieve-route vs pure-explicit-formula distinction.

No fabricated constants: A=7/3, floor 1+A/2=13/6, and the certificate thresholds
come from docs/research-opportunities.md / tools/linnik/density_payoff.py.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from math import log


# --- ledger from the repo ---
A = Fr(7, 3)           # CGL peak at sigma=5/7
SIGMA = Fr(5, 7)
FLOOR = 1 + A / 2      # = 13/6
L_FORMAL = Fr(11, 5)   # formalised sieve certificate
# density_payoff / research-opportunities: 2.199 passes, 2.198 fails (today curve)
L_PASS = Fr(2199, 1000)
L_FAIL = Fr(2198, 1000)
SLACK_APPROX = float(L_PASS - FLOOR)  # ~0.0323


def triangle_Z_size(q: float, x: float, sigma: float = float(SIGMA),
                    A: float = float(A), T: float = 1.0) -> float:
    """Crude triangle upper bound for |Z(a)| from density.

    N(sigma,T) ≪ (qT)^{A(1-sigma)}; each zero contributes ≪ x^sigma (smoothed |hat f(rho)| ~ 1
    at the critical height scale T ~ 1 for Linnik). So |Z_tri| ≲ (qT)^{A(1-sigma)} x^sigma.
    """
    return (q * T) ** (A * (1 - sigma)) * x ** sigma


def main_term(q: float, x: float) -> float:
    """Main term size for smoothed psi_f: ~ x / phi(q) ~ x/q for prime q."""
    return x / q


def needed_saving_pure_explicit(L: float, sigma: float = float(SIGMA),
                                A: float = float(A)) -> dict:
    """For pure explicit-formula Linnik: need |Z| < x roughly (up to phi(q) factors
    that cancel with the main term x/phi(q)).

    Triangle gives |Z| ≲ q^{A(1-sigma)} x^sigma, so need
        x^{1-sigma} ≫ q^{A(1-sigma)}  ⇒  L ≥ A
    (the classical Fogels-type threshold before log-free refinements / sieves).

    A power saving q^{-theta} on |Z| relative to triangle replaces A by A - theta/(1-sigma)
    in that crude comparison, or equivalently requires
        L(1-sigma) > A(1-sigma) - theta  ⇒  theta > (A - L)(1-sigma).
    """
    theta_min = (A - L) * (1 - sigma)
    return dict(
        L=L, regime="pure_explicit_crude",
        triangle_implies_L_ge=A,
        theta_vs_triangle=theta_min,
        note="crude; classical Linnik uses log-free density + sieve, not this alone",
    )


def needed_saving_sieve_route(L_target: float) -> dict:
    """Sieve-certificate route (formalised): Type II window needs L > 1 + A_eff/2,
    plus ~0.03 slack for the deep certificate.

    To reach L_target with the same slack structure as today:
        floor' = 1 + A'/2  ≤  L_target - slack
        A' ≤ 2(L_target - slack - 1)
    Saving on A: delta_A = A - A'. Relative Z-saving is not directly a power of q
    inside the sieve (density enters as a curve, not a single Z(a)). If one could
    replace the peak A by A' via a signed density-like bound, this is the required A'.
    """
    slack = SLACK_APPROX
    A_needed = 2 * (L_target - slack - 1)
    delta_A = float(A) - A_needed
    return dict(
        L_target=L_target,
        regime="sieve_certificate",
        floor_today=float(FLOOR),
        slack_approx=slack,
        A_today=float(A),
        A_needed=A_needed,
        delta_A=delta_A,
        viable=(A_needed < float(A)),
    )


def random_phase_heuristic_L(A: float = float(A), sigma: float = float(SIGMA)) -> dict:
    """Under independent random phases for chi-bar(a) x^{i gamma}:
    |Z| ~ sqrt(N) x^sigma with N = (qT)^{A(1-sigma)}.

    Pure-explicit crude: need x ≳ |Z| ⇒ x^{1-sigma} ≳ q^{A(1-sigma)/2}
    ⇒ L ≳ A/2.

    Sieve analogy: if random phases halved the density exponent (sqrt cancellation
    ≈ replacing A by A/2 in the peak), then floor → 1 + A/4.
    That is the optimistic 'conditional on random phases' deliverable.
    """
    L_pure = A / 2
    A_eff = A / 2
    floor_sieve = 1 + A_eff / 2  # = 1 + A/4
    return dict(
        assumption="iid random phases of chi-bar(a) x^{i gamma} across zeros in the box",
        N_scale="(qT)^{A(1-sigma)}",
        Z_abs_scale="sqrt(N) x^sigma",
        L_pure_explicit_crude=L_pure,
        A_eff_sqrt=A_eff,
        sieve_floor_if_A_halved=floor_sieve,
        L_sieve_optimistic=floor_sieve + SLACK_APPROX,
        note=(
            "Optimistic: sqrt cancellation replaces A by A/2 everywhere it binds. "
            "No theorem asserts random phases for distinct chi at sigma=5/7."
        ),
    )


def print_report() -> None:
    print("=== Signed Z(a) bookkeeping ===")
    print(f"A={A}, sigma={SIGMA}, floor 1+A/2={FLOOR}={float(FLOOR):.6f}")
    print(f"L_formal={L_FORMAL}, L_pass≈{float(L_PASS)}, L_fail≈{float(L_FAIL)}")
    print(f"slack≈{SLACK_APPROX:.6f}")
    print()
    print("--- Targets (sieve route) ---")
    for Lt in (float(L_FORMAL), float(L_FAIL), float(FLOOR) + 0.001, 2.167):
        r = needed_saving_sieve_route(Lt)
        print(
            f"L_target={Lt:.4f}: A_needed={r['A_needed']:.6f}, "
            f"delta_A={r['delta_A']:.6f}, viable={r['viable']}"
        )
    print()
    print("--- Pure explicit (crude) ---")
    for L in (2.2, 2.198, 2.167, float(A)):
        r = needed_saving_pure_explicit(L)
        print(f"L={L}: theta_vs_triangle > {r['theta_vs_triangle']:.6f}")
    print()
    print("--- Random-phase heuristic ---")
    h = random_phase_heuristic_L()
    for k, v in h.items():
        print(f"  {k}: {v}")
    print()
    # Quantify needed saving as power of q at x=q^L for the pure route
    print("--- Needed |Z|/|Z_tri| as q^{-theta} (pure explicit, sigma=5/7) ---")
    for name, L in [("L<11/5", 2.2 - 1e-9), ("L<2.198", 2.198), ("L<2.167", 2.167)]:
        theta = (float(A) - L) * (1 - float(SIGMA))
        # relative to today's triangle at L=11/5: today's surplus is (11/5 - A)? no
        # At fixed L, triangle |Z|/x = q^{A(1-s) - L(1-s)}; need this < 1 after saving q^{-theta}
        print(f"  {name}: need theta > {theta:.6f}  (saving factor q^{{-theta}})")


if __name__ == "__main__":
    print_report()
