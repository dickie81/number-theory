import HalfPlaneGRH
import PivotSharp
import BallRate
import BallWindowBridge

/-!
# The rebuild's Riemann hypothesis, in the words of the ball conjecture

A join between the top of the library's rebuild of L. Alpöge's proof (`docs/rh-rebuild.md`),
`HalfPlaneGRH.RHandGRH`, and the library's criteria for RH through the Hadamard kernel `K_H` (the ball conjecture,
`docs/ball-conjecture.md`), in the style of `LinnikGRH.dirichletRH_of_rhAndGRH`. The top holds RH (its first part),
and each criterion is an equivalence with Mathlib's `RiemannHypothesis`, so it gives:

* `posDef_psi`: the kernel `K_H` from the primes is positive-definite on the positive rationals
  (`BallPsi.rh_iff_posDef_psi`);
* `orbitLattice`: the orbit-lattice conjecture, `Q_k(δ_k − Σ_{n < k}c_nδ_n) ≥ Q_1(δ_1)`
  (`PivotSharp.orbitLattice_of_rh`);
* `shortest`: `w_1` is a shortest vector of the orbit lattice (`PivotSharp.rh_iff_shortest`);
* `balance`: no excess at any level, the balance of `BallRate` (`BallRate.rh_iff_balance`);
* `weil_bound`: the Weil bound `|D_m·D_n − m − n| ≤ (2 − D_1²)√(mn)` (`BallWeil.weil_bound`);
* `zetaWindowBound`, `zetaRamp_le`: the rebuild's frontier for `ζ`, and von Koch's bound for the ramp,
  `|G(x)| ≤ (‖K_H(1)‖ + B)√x` (`BallWindow.abs_zetaRamp_le_of_rh`);
* `ball`: all of them at once.
-/

namespace HalfPlaneGRH.RHandGRH

/-- **The kernel from the primes is positive-definite**, from the top. -/
theorem posDef_psi (h : RHandGRH) : BallKernel.PosDefQ BallPsi.kerHψ :=
  BallPsi.rh_iff_posDef_psi.1 h.1

/-- **The orbit-lattice conjecture**, from the top: `Q_k(δ_k − Σ_{n < k}c_nδ_n) ≥ Q_1(δ_1)`. -/
theorem orbitLattice (h : RHandGRH) (k : ℕ) (c : ℕ → ℝ) (hk : 1 ≤ k) :
    BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n) :=
  PivotSharp.orbitLattice_of_rh h.1 k c hk

/-- **`w_1` is a shortest vector of the orbit lattice**, from the top. -/
theorem shortest (h : RHandGRH) : ∀ (N : ℕ) (a : ℕ → ℤ), (∃ n ∈ Finset.Icc 1 N, a n ≠ 0) →
    BallWeil.gram 1 1 ≤ BallWeil.form N (fun n => (a n : ℝ)) :=
  PivotSharp.rh_iff_shortest.1 h.1

/-- **The balance of the ball**: no excess at any level, from the top. -/
theorem balance (h : RHandGRH) : ∀ N, BallRate.ExcessLe N 0 :=
  BallRate.rh_iff_balance.1 h.1

/-- **The Weil bound** `|D_m·D_n − m − n| ≤ (2 − D_1²)√(mn)`, from the top. -/
theorem weil_bound (h : RHandGRH) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    |BallWeil.inter m n - m - n| ≤ (2 - BallWeil.inter 1 1) * Real.sqrt ((m : ℝ) * n) :=
  BallWeil.weil_bound h.1 hm hn

/-- **The rebuild's frontier for `ζ`**, from the top. -/
theorem zetaWindowBound (h : RHandGRH) : WindowGRH.ZetaWindowBound :=
  WindowGRH.rh_iff_zetaWindowBound.1 h.1

/-- **Von Koch's bound for the ramp**, from the top: `|G(x)| ≤ (‖K_H(1)‖ + B)√x` for `x ≥ 1`. -/
theorem zetaRamp_le (h : RHandGRH) {x : ℝ} (hx : 1 ≤ x) :
    |WindowGRH.zetaFamily.G x| ≤ (‖BallHadamard.kerH 1‖ + BallWindow.bridgeB) * Real.sqrt x :=
  BallWindow.abs_zetaRamp_le_of_rh h.1 hx

/-- **The ball conjecture's criteria, from the top**: positive-definiteness of the kernel from the primes, the
orbit lattice and its shortest vector, the balance, the Weil bound, and von Koch's bound for the ramp. -/
theorem ball (h : RHandGRH) :
    BallKernel.PosDefQ BallPsi.kerHψ ∧
      (∀ (k : ℕ) (c : ℕ → ℝ), 1 ≤ k → BallWeil.gram 1 1 ≤ BallWeil.form k (fun n => if n = k then 1 else -c n)) ∧
      (∀ (N : ℕ) (a : ℕ → ℤ), (∃ n ∈ Finset.Icc 1 N, a n ≠ 0) →
        BallWeil.gram 1 1 ≤ BallWeil.form N (fun n => (a n : ℝ))) ∧
      (∀ N, BallRate.ExcessLe N 0) ∧
      (∀ m n : ℕ, 0 < m → 0 < n →
        |BallWeil.inter m n - m - n| ≤ (2 - BallWeil.inter 1 1) * Real.sqrt ((m : ℝ) * n)) ∧
      WindowGRH.ZetaWindowBound ∧
      ∀ x : ℝ, 1 ≤ x → |WindowGRH.zetaFamily.G x| ≤ (‖BallHadamard.kerH 1‖ + BallWindow.bridgeB) * Real.sqrt x :=
  ⟨h.posDef_psi, h.orbitLattice, h.shortest, h.balance, fun _ _ hm hn => h.weil_bound hm hn, h.zetaWindowBound,
    fun _ hx => h.zetaRamp_le hx⟩

end HalfPlaneGRH.RHandGRH

#print axioms HalfPlaneGRH.RHandGRH.ball
