/-
# Shell–interior coupling: Schur-type positivity and its finite chain

Plain statement. Write a quadratic form on interior ⊕ shell as `A + 2B + C`, where `A` is the interior form
(value at the interior part, squared norm `s`), `C` the shell form (squared norm `t`) and `B` the coupling. If
`A ≥ a s`, `C ≥ c t`, `B² ≤ b² s t` and `b² ≤ a c` (with `a, c ≥ 0`), then `A + 2B + C ≥ 0`
(`nonneg_of_coupling`). With a margin `m` (`b² ≤ (a − m)(c − m)`, `m ≤ a`, `m ≤ c`) the glued form keeps margin `m`:
`A + 2B + C ≥ m (s + t)` (`margin_of_coupling`). Iterating along a chain of shells, if every step satisfies the
margin coupling condition then every form in the chain is `≥ m_k` times its squared norm, in particular `≥ 0`
(`chain_nonneg`). This is abstract linear algebra; nothing here says the Weil form satisfies the hypotheses.
-/
import Mathlib

namespace ShellSchur

/-- **Coupling bound ⇒ nonnegativity.** -/
theorem nonneg_of_coupling (A B C a b c s t : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hA : a * s ≤ A) (hC : c * t ≤ C) (hB : B ^ 2 ≤ b ^ 2 * s * t) (hb : b ^ 2 ≤ a * c) :
    0 ≤ A + 2 * B + C := by
  have h1 : 0 ≤ a * s := mul_nonneg ha hs
  have h2 : 0 ≤ c * t := mul_nonneg hc ht
  have h3 : (2 * B) ^ 2 ≤ (A + C) ^ 2 := by
    have e1 : b ^ 2 * s * t ≤ a * c * (s * t) := by nlinarith [mul_nonneg hs ht]
    have e2 : 4 * (a * c * (s * t)) ≤ (a * s + c * t) ^ 2 := by nlinarith [sq_nonneg (a * s - c * t)]
    have e3 : (a * s + c * t) ^ 2 ≤ (A + C) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith); linarith
    nlinarith
  have hAC : 0 ≤ A + C := by linarith
  have := (abs_le_of_sq_le_sq' h3 hAC).1
  linarith

/-- **Coupling bound with margin.** -/
theorem margin_of_coupling (A B C a b c m s t : ℝ) (hma : m ≤ a) (hmc : m ≤ c) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hA : a * s ≤ A) (hC : c * t ≤ C) (hB : B ^ 2 ≤ b ^ 2 * s * t)
    (hb : b ^ 2 ≤ (a - m) * (c - m)) : m * (s + t) ≤ A + 2 * B + C := by
  have := nonneg_of_coupling (A - m * s) B (C - m * t) (a - m) b (c - m) s t (by linarith) (by linarith)
    hs ht (by nlinarith) (by nlinarith) hB hb
  linarith

/-- **Finite chain of shells.** `Q k v` is the `k`-th form, `N k v` its squared norm; step `k` splits `v` into an
interior part `P k v` and a shell carrying `S k v`, coupling `Bk k v` and shell form `Cq k v`. If the base form has
margin `m 0` and each step satisfies the margin coupling condition, every form has margin `m k`, hence is `≥ 0`. -/
theorem chain_nonneg {V : Type*} (Q N : ℕ → V → ℝ) (P : ℕ → V → V) (S Bk Cq : ℕ → V → ℝ) (m c b : ℕ → ℝ)
    (hN : ∀ k v, 0 ≤ N k v) (hS : ∀ k v, 0 ≤ S k v) (hm : ∀ k, 0 ≤ m k)
    (h0 : ∀ v, m 0 * N 0 v ≤ Q 0 v)
    (hQ : ∀ k v, Q (k + 1) v = Q k (P k v) + 2 * Bk k v + Cq k v)
    (hNk : ∀ k v, N (k + 1) v = N k (P k v) + S k v)
    (hC : ∀ k v, c k * S k v ≤ Cq k v)
    (hB : ∀ k v, Bk k v ^ 2 ≤ b k ^ 2 * N k (P k v) * S k v)
    (hma : ∀ k, m (k + 1) ≤ m k) (hmc : ∀ k, m (k + 1) ≤ c k)
    (hb : ∀ k, b k ^ 2 ≤ (m k - m (k + 1)) * (c k - m (k + 1))) :
    ∀ k v, 0 ≤ Q k v := by
  have key : ∀ k v, m k * N k v ≤ Q k v := by
    intro k; induction k with
    | zero => exact h0
    | succ k ih =>
      intro v
      rw [hQ, hNk]
      exact margin_of_coupling _ _ _ (m k) (b k) (c k) (m (k + 1)) _ _ (hma k) (hmc k) (hN _ _)
        (hS _ _) (ih _) (hC _ _) (hB _ _) (hb k)
  intro k v
  exact le_trans (mul_nonneg (hm k) (hN k v)) (key k v)

end ShellSchur
