/-
# The zone's exponents by pieces of the curve, from the ends of each piece

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoTypeII.ZoneOK g L d e R` asks, for every `β ∈ [1/2, 11/12]`, `(m₁, m₂)` in the region `R` and
`w ∈ [0, 4·10⁻⁶]`, for exponents `M₁`, `M₂` of the two mean squares with
`(L − m₁ − m₂)(β + w) + (m₁ + M₁)/2 + (m₂ + M₂)/2 ≤ L − 1/25000`. This file proves it piece by piece in `β`, as
`SieveCurveGlue` and `SieveHMWindow` do for the window. On a piece each variable takes one of two modes:

* `O`, orthogonality: `M = max(m, 1)`;
* `H`, Halász–Montgomery, on a piece where the curve is `A(1 − β)`: `M = max(m, A(1 − β) + b(m))`,
  `b(m) = 5/12 + m/12 + d(1 − m) + 2e`.

In either mode `M` is the larger of `m` and a function `κ(β, m)` affine in `β`. For each of the four choices of
`m_i` or `κ_i` in place of `M_i`, and each `(m₁, m₂)` with `m₁ + m₂ ≤ L`, the left side increases with `w` and is
affine in `β`, so it is at most its larger value at the two ends of the piece at `w = 4·10⁻⁶`. At an end the
inequality is linear in `(m₁, m₂)`: for a region cut out by linear inequalities, `linarith` proves it from them.

* `ZonePiece g L d e R lo hi`: the zone's exponents for `lo ≤ β ≤ hi`; `zoneOK_of_piece` (a piece on
  `[1/2, 11/12]` is the zone), `zonePiece_glue` (two pieces across `mid`, for the curve that is `g` below `mid` and
  `g′` from `mid` on).
* `zonePiece_of_ends`: a piece from its two ends, for candidates `κ_i(β, m) = u_i + v_iβ + t_im` such that
  `max(m, κ_i(β, m))` is an exponent for the mean square.
* `zonePiece_OO` (both variables by orthogonality, for every curve) and `zonePiece_HH` (both by the
  Halász–Montgomery inequality, for the curve `A(1 − β)`).
* The tactic `zends` closes the cases at the ends by `linarith`, for a region that is a conjunction of six linear
  inequalities.

`tools/linnik/gen_zone.py` writes the proof for the paper's curve (`SieveTwoZone7D.lean`).

The file imports `SieveTwoTypeII.lean`.
-/
import SieveTwoTypeII

namespace SieveTypeIIHM

/-- **The zone's exponents on a range of `β`**: `ZoneOK` for `lo ≤ β ≤ hi`. -/
def ZonePiece (g : ℝ → ℝ) (L d e : ℝ) (R : ℝ → ℝ → Prop) (lo hi : ℝ) : Prop :=
  ∀ β m₁ m₂ w : ℝ, lo ≤ β → β ≤ hi → R m₁ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 → twoBound L d e (g β) β m₁ m₂ w

/-- A piece on `[1/2, 11/12]` (`h`) is the zone's condition. -/
theorem zoneOK_of_piece {g : ℝ → ℝ} {L d e : ℝ} {R : ℝ → ℝ → Prop}
    (h : ZonePiece g L d e R (1 / 2) (11 / 12)) : ZoneOK g L d e R := h

/-- Gluing two pieces across `mid` (`h₁` on `[lo, mid]`, `h₂` on `[mid, hi]`). -/
theorem zonePiece_glue {g g' : ℝ → ℝ} {L d e lo mid hi : ℝ} {R : ℝ → ℝ → Prop}
    (h₁ : ZonePiece g L d e R lo mid) (h₂ : ZonePiece g' L d e R mid hi) :
    ZonePiece (fun β => if β < mid then g β else g' β) L d e R lo hi := by
  intro β m₁ m₂ w hβ hβ1 hR hw hw1
  by_cases hb : β < mid
  · simp only [hb, ite_true]; exact h₁ β m₁ m₂ w hβ hb.le hR hw hw1
  · simp only [hb, ite_false]; exact h₂ β m₁ m₂ w (not_lt.1 hb) hβ1 hR hw hw1

/-- A function affine in `x` on `[u, v]` is at most the larger of its values at the ends. -/
lemma affine_le_of_ends {α γ u v x c : ℝ} (hu : u ≤ x) (hv : x ≤ v) (h0 : α + γ * u ≤ c) (h1 : α + γ * v ≤ c) :
    α + γ * x ≤ c := by
  rcases le_total 0 γ with hγ | hγ
  · have := mul_le_mul_of_nonneg_left hv hγ
    linarith
  · have := mul_le_mul_of_nonpos_left hu hγ
    linarith

/-- **A piece of a zone from its two ends.** Let the region lie in `m₁ + m₂ ≤ L` (`hR`), and let
`κ_i(β, m) = u_i + v_iβ + t_im` be such that `max(m, κ_i(β, m))` is an exponent for the mean square on `lo ≤ β ≤ hi`
(`hκ₁`, `hκ₂`). If at `β ∈ {lo, hi}`, for `(m₁, m₂)` in the region and for the four choices `c_i ∈ {m_i, κ_i(β, m_i)}`,
the exponent `(L − m₁ − m₂)(β + 4·10⁻⁶) + (m₁ + c₁)/2 + (m₂ + c₂)/2` is at most `L − 1/25000` (`hc`), the piece
holds. -/
theorem zonePiece_of_ends {g : ℝ → ℝ} {L d e lo hi u₁ v₁ t₁ u₂ v₂ t₂ : ℝ} {R : ℝ → ℝ → Prop}
    (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hκ₁ : ∀ β m, lo ≤ β → β ≤ hi → SqExp d e (g β) m (max m (u₁ + v₁ * β + t₁ * m)))
    (hκ₂ : ∀ β m, lo ≤ β → β ≤ hi → SqExp d e (g β) m (max m (u₂ + v₂ * β + t₂ * m)))
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂, (c₁ = m₁ ∨ c₁ = u₁ + v₁ * β + t₁ * m₁) →
      (c₂ = m₂ ∨ c₂ = u₂ + v₂ * β + t₂ * m₂) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece g L d e R lo hi := by
  intro β m₁ m₂ w hβ hβ1 hRm hw hw1
  refine ⟨max m₁ (u₁ + v₁ * β + t₁ * m₁), max m₂ (u₂ + v₂ * β + t₂ * m₂), hκ₁ β m₁ hβ hβ1, hκ₂ β m₂ hβ hβ1, ?_⟩
  have hρ : 0 ≤ L - m₁ - m₂ := by linarith [hR m₁ m₂ hRm]
  have hW : (L - m₁ - m₂) * (β + w) ≤ (L - m₁ - m₂) * (β + 4 / 10 ^ 6) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ
  -- the four choices, each affine in `β`
  have E11 := affine_le_of_ends (α := (L - m₁ - m₂) * (4 / 10 ^ 6) + m₁ + m₂) (γ := L - m₁ - m₂)
    (c := L - 1 / 25000) hβ hβ1
    (by have := hc lo (Or.inl rfl) m₁ m₂ hRm m₁ m₂ (Or.inl rfl) (Or.inl rfl); linarith)
    (by have := hc hi (Or.inr rfl) m₁ m₂ hRm m₁ m₂ (Or.inl rfl) (Or.inl rfl); linarith)
  have E12 := affine_le_of_ends (α := (L - m₁ - m₂) * (4 / 10 ^ 6) + m₁ + (m₂ + (u₂ + t₂ * m₂)) / 2)
    (γ := L - m₁ - m₂ + v₂ / 2) (c := L - 1 / 25000) hβ hβ1
    (by have := hc lo (Or.inl rfl) m₁ m₂ hRm m₁ (u₂ + v₂ * lo + t₂ * m₂) (Or.inl rfl) (Or.inr rfl); linarith)
    (by have := hc hi (Or.inr rfl) m₁ m₂ hRm m₁ (u₂ + v₂ * hi + t₂ * m₂) (Or.inl rfl) (Or.inr rfl); linarith)
  have E21 := affine_le_of_ends (α := (L - m₁ - m₂) * (4 / 10 ^ 6) + (m₁ + (u₁ + t₁ * m₁)) / 2 + m₂)
    (γ := L - m₁ - m₂ + v₁ / 2) (c := L - 1 / 25000) hβ hβ1
    (by have := hc lo (Or.inl rfl) m₁ m₂ hRm (u₁ + v₁ * lo + t₁ * m₁) m₂ (Or.inr rfl) (Or.inl rfl); linarith)
    (by have := hc hi (Or.inr rfl) m₁ m₂ hRm (u₁ + v₁ * hi + t₁ * m₁) m₂ (Or.inr rfl) (Or.inl rfl); linarith)
  have E22 := affine_le_of_ends
    (α := (L - m₁ - m₂) * (4 / 10 ^ 6) + (m₁ + (u₁ + t₁ * m₁)) / 2 + (m₂ + (u₂ + t₂ * m₂)) / 2)
    (γ := L - m₁ - m₂ + v₁ / 2 + v₂ / 2) (c := L - 1 / 25000) hβ hβ1
    (by have := hc lo (Or.inl rfl) m₁ m₂ hRm (u₁ + v₁ * lo + t₁ * m₁) (u₂ + v₂ * lo + t₂ * m₂) (Or.inr rfl)
          (Or.inr rfl)
        linarith)
    (by have := hc hi (Or.inr rfl) m₁ m₂ hRm (u₁ + v₁ * hi + t₁ * m₁) (u₂ + v₂ * hi + t₂ * m₂) (Or.inr rfl)
          (Or.inr rfl)
        linarith)
  rcases max_cases m₁ (u₁ + v₁ * β + t₁ * m₁) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
    rcases max_cases m₂ (u₂ + v₂ * β + t₂ * m₂) with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h1, h2] <;> linarith

/-- Orthogonality's exponent: `max(m, 1)`, written with the candidate `1 + 0·β + 0·m`. -/
lemma sqExp_orth (d e g β m : ℝ) : SqExp d e g m (max m (1 + 0 * β + 0 * m)) :=
  Or.inl ⟨le_max_of_le_right (le_of_eq (by ring)), le_max_left _ _⟩

/-- Halász–Montgomery's exponent on a piece `A(1 − β)`: `max(m, A(1 − β) + b(m))`, with the candidate written
`(A + 5/12 + d + 2e) + (−A)β + (1/12 − d)m`. -/
lemma sqExp_hm (A d e β m : ℝ) :
    SqExp d e (A * (1 - β)) m (max m ((A + 5 / 12 + d + 2 * e) + (-A) * β + (1 / 12 - d) * m)) :=
  Or.inr ⟨le_max_left _ _, le_max_of_le_right (le_of_eq (by ring))⟩

/-- **Both variables by orthogonality**, for every curve: the inequalities at the two ends with `c_i ∈ {m_i, 1}`,
on a region in `m₁ + m₂ ≤ L` (`hR`). -/
theorem zonePiece_OO (g : ℝ → ℝ) {L d e lo hi : ℝ} {R : ℝ → ℝ → Prop} (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂, (c₁ = m₁ ∨ c₁ = 1) → (c₂ = m₂ ∨ c₂ = 1) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece g L d e R lo hi :=
  zonePiece_of_ends hR (fun β m _ _ => sqExp_orth d e (g β) β m) (fun β m _ _ => sqExp_orth d e (g β) β m)
    (fun β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂ => hc β hb m₁ m₂ hRm c₁ c₂
      (hc₁.imp id fun h => h.trans (by ring)) (hc₂.imp id fun h => h.trans (by ring)))

/-- **Both variables by the Halász–Montgomery inequality**, on a piece `A(1 − β)`: the inequalities at the two ends
with `c_i ∈ {m_i, A(1 − β) + 5/12 + m_i/12 + d(1 − m_i) + 2e}`, on a region in `m₁ + m₂ ≤ L` (`hR`). -/
theorem zonePiece_HH {A L d e lo hi : ℝ} {R : ℝ → ℝ → Prop} (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂,
      (c₁ = m₁ ∨ c₁ = A * (1 - β) + (5 / 12 + m₁ / 12 + d * (1 - m₁) + 2 * e)) →
      (c₂ = m₂ ∨ c₂ = A * (1 - β) + (5 / 12 + m₂ / 12 + d * (1 - m₂) + 2 * e)) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece (fun β => A * (1 - β)) L d e R lo hi :=
  zonePiece_of_ends hR (fun β m _ _ => sqExp_hm A d e β m) (fun β m _ _ => sqExp_hm A d e β m)
    (fun β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂ => hc β hb m₁ m₂ hRm c₁ c₂
      (hc₁.imp id fun h => h.trans (by ring)) (hc₂.imp id fun h => h.trans (by ring)))

set_option hygiene false in
/-- The cases of `zonePiece_OO` and `zonePiece_HH` at the ends, for a region that is a conjunction of six linear
inequalities: two values of `β` and two candidates for each variable, each case by `linarith` from the six. -/
macro "zends" : tactic =>
  `(tactic| (intro β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂
             obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hRm
             rcases hb with rfl | rfl <;> rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl <;> linarith))

end SieveTypeIIHM

#print axioms SieveTypeIIHM.zonePiece_glue
#print axioms SieveTypeIIHM.zonePiece_OO
#print axioms SieveTypeIIHM.zonePiece_HH
