/-
# The zone's exponents with the fourth moment, by pieces of the curve

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTwoPieces` proves the zone's condition `ZoneOK` piece by piece in `β`, from the cases at the two ends of each
piece. This file does the same for `ZoneOK4`, the condition with the fourth moment as a third bound
(`SieveTwoZone4.SqExp4`). On a piece each variable takes one of three modes, in each of which its exponent is the
larger of `m` and a candidate affine in `β`:

* `O`, orthogonality: `M = max(m, 1)`;
* `E`, the fourth moment, for a variable of length at most `√q` (`m ≤ 1/2`) on a piece where the curve is
  `A(1 − β)`: `M = max(m, A(1 − β)/2 + 1/2 + 2e)`.

Since the fourth moment's candidate is an exponent only for `m ≤ 1/2`, the candidates here are asked of the points of
the region only (`zonePiece4_of_ends`).

* `ZonePiece4 g L d e R lo hi`: `ZoneOK4` for `lo ≤ β ≤ hi`; `zoneOK4_of_piece`, `zonePiece4_glue`.
* `zonePiece4_of_ends`: a piece from its two ends, for candidates `κ_i(β, m) = u_i + v_iβ + t_im` that are
  exponents on the region.
* `zonePiece4_OO` (both variables by orthogonality, for every curve), `zonePiece4_OE` (the first by orthogonality,
  the second by the fourth moment) and `zonePiece4_HE` (the first by the Halász–Montgomery inequality, the second by
  the fourth moment), the last two on a piece `A(1 − β)` and a region with `m₂ ≤ 1/2`.

The file imports `SieveTwoTypeII4.lean` and `SieveTwoPieces.lean`.
-/
import SieveTwoTypeII4
import SieveTwoPieces

namespace SieveTypeIIHM

/-- **The zone's exponents with the fourth moment on a range of `β`**: `ZoneOK4` for `lo ≤ β ≤ hi`. -/
def ZonePiece4 (g : ℝ → ℝ) (L d e : ℝ) (R : ℝ → ℝ → Prop) (lo hi : ℝ) : Prop :=
  ∀ β m₁ m₂ w : ℝ, lo ≤ β → β ≤ hi → R m₁ m₂ → 0 ≤ w → w ≤ 4 / 10 ^ 6 → twoBound4 L d e (g β) β m₁ m₂ w

/-- A piece on `[1/2, 11/12]` (`h`) is the zone's condition. -/
theorem zoneOK4_of_piece {g : ℝ → ℝ} {L d e : ℝ} {R : ℝ → ℝ → Prop}
    (h : ZonePiece4 g L d e R (1 / 2) (11 / 12)) : ZoneOK4 g L d e R := h

/-- Gluing two pieces across `mid` (`h₁` on `[lo, mid]`, `h₂` on `[mid, hi]`). -/
theorem zonePiece4_glue {g g' : ℝ → ℝ} {L d e lo mid hi : ℝ} {R : ℝ → ℝ → Prop}
    (h₁ : ZonePiece4 g L d e R lo mid) (h₂ : ZonePiece4 g' L d e R mid hi) :
    ZonePiece4 (fun β => if β < mid then g β else g' β) L d e R lo hi := by
  intro β m₁ m₂ w hβ hβ1 hR hw hw1
  by_cases hb : β < mid
  · simp only [hb, ite_true]; exact h₁ β m₁ m₂ w hβ hb.le hR hw hw1
  · simp only [hb, ite_false]; exact h₂ β m₁ m₂ w (not_lt.1 hb) hβ1 hR hw hw1

/-- **A piece of the zone with the fourth moment, from its two ends.** As `zonePiece_of_ends`, with candidates that
are exponents (`SqExp4`) at the points of the region only (`hκ₁`, `hκ₂`). -/
theorem zonePiece4_of_ends {g : ℝ → ℝ} {L d e lo hi u₁ v₁ t₁ u₂ v₂ t₂ : ℝ} {R : ℝ → ℝ → Prop}
    (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hκ₁ : ∀ β m₁ m₂, lo ≤ β → β ≤ hi → R m₁ m₂ → SqExp4 d e (g β) m₁ (max m₁ (u₁ + v₁ * β + t₁ * m₁)))
    (hκ₂ : ∀ β m₁ m₂, lo ≤ β → β ≤ hi → R m₁ m₂ → SqExp4 d e (g β) m₂ (max m₂ (u₂ + v₂ * β + t₂ * m₂)))
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂, (c₁ = m₁ ∨ c₁ = u₁ + v₁ * β + t₁ * m₁) →
      (c₂ = m₂ ∨ c₂ = u₂ + v₂ * β + t₂ * m₂) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece4 g L d e R lo hi := by
  intro β m₁ m₂ w hβ hβ1 hRm hw hw1
  refine ⟨max m₁ (u₁ + v₁ * β + t₁ * m₁), max m₂ (u₂ + v₂ * β + t₂ * m₂), hκ₁ β m₁ m₂ hβ hβ1 hRm,
    hκ₂ β m₁ m₂ hβ hβ1 hRm, ?_⟩
  have hρ : 0 ≤ L - m₁ - m₂ := by linarith [hR m₁ m₂ hRm]
  have hW : (L - m₁ - m₂) * (β + w) ≤ (L - m₁ - m₂) * (β + 4 / 10 ^ 6) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ
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

/-- Orthogonality's exponent in `SqExp4`: `max(m, 1)`. -/
lemma sqExp4_orth (d e g β m : ℝ) : SqExp4 d e g m (max m (1 + 0 * β + 0 * m)) :=
  Or.inl (sqExp_orth d e g β m)

/-- The fourth moment's exponent on a piece `A(1 − β)`, for `m ≤ 1/2` and `A(1 − β) ≥ 0`:
`max(m, A(1 − β)/2 + 1/2 + 2e)`, with the candidate written `(A/2 + 1/2 + 2e) + (−A/2)β + 0·m`. -/
lemma sqExp4_energy (A d e β m : ℝ) (hm : m ≤ 1 / 2) :
    SqExp4 d e (A * (1 - β)) m (max m ((A / 2 + 1 / 2 + 2 * e) + (-A / 2) * β + 0 * m)) := by
  refine Or.inr ⟨le_max_left _ _, le_max_of_le_right (le_of_eq ?_)⟩
  rw [max_eq_right hm]
  ring

/-- **Both variables by orthogonality**, for every curve: `zonePiece_OO` for `ZoneOK4`. -/
theorem zonePiece4_OO (g : ℝ → ℝ) {L d e lo hi : ℝ} {R : ℝ → ℝ → Prop} (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂, (c₁ = m₁ ∨ c₁ = 1) → (c₂ = m₂ ∨ c₂ = 1) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece4 g L d e R lo hi :=
  zonePiece4_of_ends hR (fun β m₁ _ _ _ _ => sqExp4_orth d e (g β) β m₁)
    (fun β _ m₂ _ _ _ => sqExp4_orth d e (g β) β m₂)
    (fun β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂ => hc β hb m₁ m₂ hRm c₁ c₂
      (hc₁.imp id fun h => h.trans (by ring)) (hc₂.imp id fun h => h.trans (by ring)))

/-- **The first variable by orthogonality, the second by the fourth moment**, on a piece `A(1 − β)` and a region in
`m₁ + m₂ ≤ L` (`hR`) with `m₂ ≤ 1/2` (`hR₂`): the inequalities at the two ends with `c₁ ∈ {m₁, 1}` and
`c₂ ∈ {m₂, A(1 − β)/2 + 1/2 + 2e}`. -/
theorem zonePiece4_OE {A L d e lo hi : ℝ} {R : ℝ → ℝ → Prop} (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hR₂ : ∀ m₁ m₂, R m₁ m₂ → m₂ ≤ 1 / 2)
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂, (c₁ = m₁ ∨ c₁ = 1) →
      (c₂ = m₂ ∨ c₂ = A * (1 - β) / 2 + 1 / 2 + 2 * e) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece4 (fun β => A * (1 - β)) L d e R lo hi :=
  zonePiece4_of_ends hR (fun β m₁ _ _ _ _ => sqExp4_orth d e (A * (1 - β)) β m₁)
    (fun β m₁ m₂ _ _ hRm => sqExp4_energy A d e β m₂ (hR₂ m₁ m₂ hRm))
    (fun β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂ => hc β hb m₁ m₂ hRm c₁ c₂
      (hc₁.imp id fun h => h.trans (by ring)) (hc₂.imp id fun h => h.trans (by ring)))

/-- **The first variable by the Halász–Montgomery inequality, the second by the fourth moment**, on a piece
`A(1 − β)` and a region in `m₁ + m₂ ≤ L` (`hR`) with `m₂ ≤ 1/2` (`hR₂`): the inequalities at the two ends with
`c₁ ∈ {m₁, A(1 − β) + 5/12 + m₁/12 + d(1 − m₁) + 2e}` and `c₂ ∈ {m₂, A(1 − β)/2 + 1/2 + 2e}`. -/
theorem zonePiece4_HE {A L d e lo hi : ℝ} {R : ℝ → ℝ → Prop} (hR : ∀ m₁ m₂, R m₁ m₂ → m₁ + m₂ ≤ L)
    (hR₂ : ∀ m₁ m₂, R m₁ m₂ → m₂ ≤ 1 / 2)
    (hc : ∀ β, (β = lo ∨ β = hi) → ∀ m₁ m₂, R m₁ m₂ → ∀ c₁ c₂,
      (c₁ = m₁ ∨ c₁ = A * (1 - β) + (5 / 12 + m₁ / 12 + d * (1 - m₁) + 2 * e)) →
      (c₂ = m₂ ∨ c₂ = A * (1 - β) / 2 + 1 / 2 + 2 * e) →
      (L - m₁ - m₂) * (β + 4 / 10 ^ 6) + (m₁ + c₁) / 2 + (m₂ + c₂) / 2 ≤ L - 1 / 25000) :
    ZonePiece4 (fun β => A * (1 - β)) L d e R lo hi :=
  zonePiece4_of_ends hR (fun β m₁ _ _ _ _ => Or.inl (sqExp_hm A d e β m₁))
    (fun β m₁ m₂ _ _ hRm => sqExp4_energy A d e β m₂ (hR₂ m₁ m₂ hRm))
    (fun β hb m₁ m₂ hRm c₁ c₂ hc₁ hc₂ => hc β hb m₁ m₂ hRm c₁ c₂
      (hc₁.imp id fun h => h.trans (by ring)) (hc₂.imp id fun h => h.trans (by ring)))

end SieveTypeIIHM

#print axioms SieveTypeIIHM.zonePiece4_OO
#print axioms SieveTypeIIHM.zonePiece4_OE
#print axioms SieveTypeIIHM.zonePiece4_HE
