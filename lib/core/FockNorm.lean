import WeylSandwich

/-!
# The Fock norm of the highest weight vector

For an antitone shape `ν` (block-wise, `Φ` the blocks; one block is `Φ = Unit`), the Fock norm `κ = ⟨hw_ν, hw_ν⟩`
of the highest weight vector (`WeylSandwich.kapN`) has its classical value: block by block,
`κ·∏_{i<j} (ν_i − ν_j + j − i) = ∏_b ν_b!·∏_{i<j} (ν_i + j − i)`, equivalently `κ = ∏_i ℓ_i!/∏_{i<j} (ℓ_i − ℓ_j)`
with `ℓ_i = ν_i + k − 1 − i`, the product of the hook lengths of `ν`.

**Main results.**
* *The formula* (`kapN_formula`): the identity above, multiplied over the blocks, for every antitone `ν`. It is the
  hypothesis of `WeylSandwich.sandExp_le`.
* *The exponent* (`sandExp_le'`): `sandExp_le` without its hypothesis, so the sandwich exponent is at most
  `Σ_τ (Σ_{i<j} ⌊log_p(ν_{τ,i} + j − i)⌋ + (k − 1)·Σ_b ⌊log_p ν_{τ,b}⌋)` for every antitone `ν`.

**Route** (the Capelli identity, one column at a time). Let `s` be the last row of a block `τ` with `ν_{τ,s} > 0`,
and `ν'` the shape with one column fewer in that block (`ν'_{τ,b} = ν_{τ,b} − 1`, truncated). Then `hw_ν = D·hw_ν'`
for the leading minor `D = D_{τ,s}` of size `s + 1` (`hw_peel`), and multiplication by `D` is Fock-adjoint to the
dual minor `D(∂)` (`fock_minor_left`, from `⟨P·x_q, Q⟩ = ⟨P, ∂_q Q⟩`), so `κ(ν) = ⟨hw_ν', D(∂) hw_ν⟩`.
* *The Capelli identity* (`capelli`): in any ring with commuting `x_{a,t}` and `∂_{b,t}·x_{a,u} = x_{a,u}·∂_{b,t} +
  [a = b, u = t]`, alternated over the first indices, the normally ordered products `Σ_t x_{w,t}·∂_{g,t}` (`capP`)
  and the shifted polarisation words `∏_j (E_{w j, g j} + (k − 1 − j)·[w j = g j])` (`capL`, factors in increasing
  `j`, `E_{a,b} = Σ_t x_{a,t}·∂_{b,t}`) agree. By induction on the size, peeling the first column (`capP_cons`,
  `capL_cons`, `alt_succ`); the commutator terms contract under the alternation to the diagonal shift
  (`alt_contract`).
* *At the highest weight vector* (`capelli_hw`): for the leading block, the left side is `D·D(∂)`; on `hw_ν` the
  raising polarisations vanish (`WeylSpan.polar_eq_zero`), the diagonal ones are the column degrees (`euler_col`) and
  the rows past `s` do not occur (`pderiv_eq_zero_of_row`), so only `σ = 1` survives (`ofFn_prod_apply`):
  `D·D(∂) hw_ν = c·hw_ν` with `c = ∏_{j ≤ s} (ν_{τ,j} + s − j)`.
* *The recursion* (`fock_hw_peel`): cancelling `D`, `D(∂) hw_ν = c·hw_ν'`, so `κ(ν) = c·κ(ν')`. Induction on `|ν|`
  (`fock_hw_eq_prod`), with the row-by-row telescoping of the product formula (`prod_rowF_peel`), gives
  `κ(ν) = ∏_τ ∏_i rowF(ν_τ, i)`, `rowF(μ, i) = μ_i!·∏_{j>i} (μ_i + j − i)/(μ_i − μ_j + j − i)`.
-/

namespace FockNorm

open MvPolynomial WeylFock WeylSandwich Equiv

/-! ## The Capelli identity in a ring -/

section Capelli

variable {R : Type*} [Ring R] {I S : Type*} [DecidableEq I] [Fintype S] [DecidableEq S] (x d : I → S → R)

/-- **A word** `x_{w 0, s 0}⋯x_{w (k−1), s (k−1)}`, in this order. -/
def xw {k : ℕ} (w : Fin k → I) (s : Fin k → S) : R := (List.ofFn fun j => x (w j) (s j)).prod

/-- **The normally ordered product** `Σ_s x_{w,s}·∂_{g,s}`, all `x`'s to the left of all `∂`'s. For a square block
and alternated rows it is `det(x)·det(∂)`. -/
def capP {k : ℕ} (w g : Fin k → I) : R := ∑ s : Fin k → S, xw x w s * xw d g s

/-- **The polarisation** `E_{a,b} = Σ_t x_{a,t}·∂_{b,t}`. -/
def polE (a b : I) : R := ∑ t, x a t * d b t

/-- **The shifted polarisation word** `∏_j (E_{w j, g j} + (k − 1 − j)·[w j = g j])`, factors in increasing `j`. -/
def capL {k : ℕ} (w g : Fin k → I) : R :=
  (List.ofFn fun j : Fin k => polE x d (w j) (g j) + if w j = g j then ((k - 1 - j : ℕ) : R) else 0).prod

/-- **The alternation** `Σ_σ sign(σ)·F(r ∘ σ)` over the rows. -/
def alt {k : ℕ} (F : (Fin k → I) → R) (r : Fin k → I) : R :=
  ∑ σ : Perm (Fin k), (Perm.sign σ : ℤ) • F (r ∘ σ)

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **Peeling the first letter of a word.** -/
theorem xw_cons {k : ℕ} (a : I) (t : S) (w : Fin k → I) (s : Fin k → S) :
    xw x (Fin.cons a w) (Fin.cons t s) = x a t * xw x w s := by
  simp [xw, List.ofFn_succ]

omit [Fintype S] in
/-- **Moving `∂_{b,t}` across a word**: each letter `x_{b,t}` it meets leaves the word with that letter replaced by
the `x_{a,t}` in front. -/
theorem d_xw (hxx : ∀ a s b t, Commute (x a s) (x b t))
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) :
    ∀ {k : ℕ} (a b : I) (t : S) (w : Fin k → I) (s : Fin k → S),
      x a t * (d b t * xw x w s) = x a t * xw x w s * d b t +
        ∑ j, if w j = b ∧ s j = t then xw x (Function.update w j a) s else 0
  | 0, a, b, t, w, s => by simp [xw]
  | k + 1, a, b, t, w, s => by
    obtain ⟨w0, w', rfl⟩ : ∃ w0 w', w = Fin.cons w0 w' := ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    obtain ⟨s0, s', rfl⟩ : ∃ s0 s', s = Fin.cons s0 s' := ⟨s 0, Fin.tail s, (Fin.cons_self_tail s).symm⟩
    have ih := d_xw hxx hdx a b t w' s'
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ← Fin.cons_update, Fin.update_cons_zero, xw_cons]
    have h1 : d b t * (x w0 s0 * xw x w' s') =
        x w0 s0 * (d b t * xw x w' s') + if w0 = b ∧ s0 = t then xw x w' s' else 0 := by
      rw [← mul_assoc, hdx, add_mul, mul_assoc]
      split_ifs <;> simp
    rw [h1, mul_add, ← mul_assoc (x a t) (x w0 s0), (hxx a t w0 s0).eq, mul_assoc, ih, mul_add, Finset.mul_sum]
    have h2 : x a t * (if w0 = b ∧ s0 = t then xw x w' s' else 0) =
        if w0 = b ∧ s0 = t then x a s0 * xw x w' s' else 0 := by
      split_ifs with h
      · rw [h.2]
      · rw [mul_zero]
    rw [h2]
    have h3 : ∀ j, x w0 s0 * (if w' j = b ∧ s' j = t then xw x (Function.update w' j a) s' else 0) =
        if w' j = b ∧ s' j = t then x w0 s0 * xw x (Function.update w' j a) s' else 0 := fun j => by
      split_ifs <;> simp
    simp only [h3]
    rw [← mul_assoc (x w0 s0), ← mul_assoc (x w0 s0), ← (hxx a t w0 s0).eq, mul_assoc (x a t) (x w0 s0)]
    abel

omit [DecidableEq I] [DecidableEq S] in
/-- **Summing over tuples by their first entry.** -/
theorem sum_cons {M : Type*} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → S) → M) :
    ∑ s, f s = ∑ t, ∑ s' : Fin k → S, f (Fin.cons t s') := by
  rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **The recursion of the normally ordered product**: `E_{a,b}·P(w, g) = P(a :: w, b :: g) +
Σ_{j : w j = b} P(w[j ↦ a], g)`. -/
theorem capP_cons (hxx : ∀ a s b t, Commute (x a s) (x b t))
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) {k : ℕ} (a b : I)
    (w g : Fin k → I) :
    polE x d a b * capP x d w g = capP x d (Fin.cons a w) (Fin.cons b g) +
      ∑ j, if w j = b then capP x d (Function.update w j a) g else 0 := by
  have e1 : polE x d a b * capP x d w g = ∑ t, ∑ s : Fin k → S, x a t * (d b t * xw x w s) * xw d g s := by
    simp only [polE, capP, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [e1, capP, sum_cons]
  simp only [d_xw x d hxx hdx, add_mul, Finset.sum_add_distrib, Finset.sum_mul, xw_cons]
  congr 1
  · exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by simp only [mul_assoc]
  · have key : ∀ (s : Fin k → S) (j : Fin k), (∑ t, (if w j = b ∧ s j = t then
        xw x (Function.update w j a) s else 0) * xw d g s) =
        if w j = b then xw x (Function.update w j a) s * xw d g s else 0 := fun s j => by
      by_cases h : w j = b <;> simp [h]
    have r1 : ∀ j, (if w j = b then capP x d (Function.update w j a) g else 0) =
        ∑ s, if w j = b then xw x (Function.update w j a) s * xw d g s else 0 := fun j => by
      split_ifs <;> simp [capP]
    calc ∑ t, ∑ s : Fin k → S, ∑ j, (if w j = b ∧ s j = t then xw x (Function.update w j a) s else 0) *
          xw d g s
        = ∑ s : Fin k → S, ∑ t, ∑ j, (if w j = b ∧ s j = t then xw x (Function.update w j a) s else 0) *
          xw d g s := Finset.sum_comm
      _ = ∑ s : Fin k → S, ∑ j, if w j = b then xw x (Function.update w j a) s * xw d g s else 0 :=
          Finset.sum_congr rfl fun s _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => key s j
      _ = ∑ j, ∑ s : Fin k → S, if w j = b then xw x (Function.update w j a) s * xw d g s else 0 :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun j _ => (r1 j).symm

omit [DecidableEq S] in
/-- **The recursion of the shifted polarisation word**: the first factor carries the shift `k`. -/
theorem capL_cons {k : ℕ} (a b : I) (w g : Fin k → I) :
    capL x d (Fin.cons a w) (Fin.cons b g) = (polE x d a b + if a = b then (k : R) else 0) * capL x d w g := by
  have e : ∀ j : ℕ, k - 1 - j = k - (j + 1) := fun j => by omega
  simp only [capL, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero,
    Nat.add_sub_cancel, Nat.sub_zero]
  simp only [e]

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **The alternation by the first entry**: `σ = (swap 0 p)·(1 ⊕ e)` (`Equiv.Perm.decomposeFin`), so
`alt F r = Σ_p sign(swap 0 p)·alt (F ∘ cons (r p)) ρ_p` with `ρ_p(y) = r(swap 0 p (y + 1))`. -/
theorem alt_succ {k : ℕ} (F : (Fin (k + 1) → I) → R) (r : Fin (k + 1) → I) :
    alt F r = ∑ p, (Perm.sign (swap 0 p) : ℤ) •
      alt (fun w => F (Fin.cons (r p) w)) fun y => r (swap 0 p y.succ) := by
  unfold alt
  rw [← Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hr : r ∘ ⇑(Perm.decomposeFin.symm (p, e)) = Fin.cons (r p) ((fun y => r (swap 0 p y.succ)) ∘ ⇑e) := by
    funext i
    refine Fin.cases ?_ (fun y => ?_) i <;> simp
  rw [hr, Perm.decomposeFin.symm_sign, Perm.sign_swap', smul_smul]
  congr 1
  by_cases h : p = 0
  · subst h; simp
  · simp [h, Ne.symm h]

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **The alternation is left linear.** -/
theorem alt_mul_left {k : ℕ} (c : R) (F : (Fin k → I) → R) (r : Fin k → I) :
    alt (fun w => c * F w) r = c * alt F r := by
  simp only [alt, Finset.mul_sum, mul_smul_comm]

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **The alternation is additive.** -/
theorem alt_sub {k : ℕ} (F G : (Fin k → I) → R) (r : Fin k → I) :
    alt (fun w => F w - G w) r = alt F r - alt G r := by
  simp only [alt, smul_sub, Finset.sum_sub_distrib]

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **The alternation is alternating**: `alt F (r ∘ π) = sign(π)·alt F r`. -/
theorem alt_comp_perm {k : ℕ} (F : (Fin k → I) → R) (r : Fin k → I) (π : Perm (Fin k)) :
    alt F (r ∘ π) = (Perm.sign π : ℤ) • alt F r := by
  unfold alt
  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft π⁻¹)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_smul]
  have h1 : ((Perm.sign (π⁻¹ * σ) : ℤˣ) : ℤ) = (Perm.sign π : ℤ) * (Perm.sign σ : ℤ) := by
    rw [Perm.sign_mul, Perm.sign_inv, Units.val_mul]
  have h2 : (r ∘ ⇑π) ∘ ⇑(π⁻¹ * σ) = r ∘ ⇑σ := by
    funext y
    simp
  simp only [Equiv.coe_mulLeft, h1, h2]

omit [Fintype S] [DecidableEq S] in
/-- **Alternating the commutator terms**: `alt (Σ_{j : w j = b} Q(w[j ↦ a])) ρ = Σ_{i : ρ i = b} alt Q (ρ[i ↦ a])`,
reindexing `j ↦ σ j`. -/
theorem alt_update {k : ℕ} (Q : (Fin k → I) → R) (b a : I) (ρ : Fin k → I) :
    alt (fun w => ∑ j, if w j = b then Q (Function.update w j a) else 0) ρ =
      ∑ i, if ρ i = b then alt Q (Function.update ρ i a) else 0 := by
  have h : ∀ σ : Perm (Fin k), (∑ j, if (ρ ∘ σ) j = b then Q (Function.update (ρ ∘ σ) j a) else 0) =
      ∑ i, if ρ i = b then Q (Function.update ρ i a ∘ σ) else 0 := fun σ => by
    rw [← Equiv.sum_comp σ (fun i => if ρ i = b then Q (Function.update ρ i a ∘ σ) else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, Function.update_comp_equiv, Equiv.symm_apply_apply]
  unfold alt
  refine (Finset.sum_congr rfl fun σ _ => by beta_reduce; rw [h σ]).trans ?_
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **Replacing an entry of `ρ_p` by `r p`** gives `ρ_q` up to a permutation of sign `−sign(swap 0 p)·sign(swap 0 q)`,
`q = swap 0 p (i + 1)`: the two tuples are `r ∘ swap 0 p ∘ swap 0 (i + 1)` and `r ∘ swap 0 q` on the successors, and
`swap 0 q·swap 0 p·swap 0 (i + 1)` fixes `0`. -/
theorem alt_swap_update {k : ℕ} (Q : (Fin k → I) → R) (r : Fin (k + 1) → I) (p : Fin (k + 1)) (i : Fin k) :
    alt Q (Function.update (fun y => r (swap 0 p y.succ)) i (r p)) =
      -((Perm.sign (swap 0 p) : ℤ) * (Perm.sign (swap 0 (swap 0 p i.succ)) : ℤ)) •
        alt Q fun y => r (swap 0 (swap 0 p i.succ) y.succ) := by
  set q := swap 0 p i.succ with hq
  set α : Perm (Fin (k + 1)) := swap 0 q * swap 0 p * swap 0 i.succ with hα
  have hα0 : α 0 = 0 := by simp [hα, hq]
  set π := (Perm.decomposeFin α).2
  have h1 : (Perm.decomposeFin α).1 = 0 := by
    have := Perm.decomposeFin_symm_apply_zero (Perm.decomposeFin α).1 (Perm.decomposeFin α).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at this
    rw [← this, hα0]
  have hd : Perm.decomposeFin.symm (0, π) = α := by
    rw [← h1, Prod.mk.eta, Equiv.symm_apply_apply]
  have hπ : ∀ y, α y.succ = (π y).succ := fun y => by
    rw [← hd, Perm.decomposeFin_symm_apply_succ, swap_self, refl_apply]
  have hsign : (Perm.sign π : ℤ) = -((Perm.sign (swap 0 p) : ℤ) * (Perm.sign (swap 0 q) : ℤ)) := by
    have h2 : Perm.sign π = Perm.sign α := by rw [← hd, Perm.decomposeFin.symm_sign]; simp
    rw [h2, hα, Perm.sign_mul, Perm.sign_mul, Perm.sign_swap (Fin.succ_ne_zero i).symm]
    push_cast
    ring
  have hfun : Function.update (fun y => r (swap 0 p y.succ)) i (r p) =
      (fun y => r (swap 0 q y.succ)) ∘ ⇑π := by
    funext y
    simp only [Function.comp_apply, ← hπ, hα, Perm.mul_apply, swap_apply_self]
    by_cases hy : y = i
    · subst hy
      simp
    · rw [Function.update_of_ne hy,
        swap_apply_of_ne_of_ne (Fin.succ_ne_zero y) (fun h => hy (Fin.succ_injective _ h))]
  rw [hfun, alt_comp_perm, hsign]

omit [DecidableEq I] [Fintype S] [DecidableEq S] in
/-- **Counting the pairs `(p, i)`**: `i ↦ swap 0 p (i + 1)` enumerates the `q ≠ p`, so every `q` is met `k` times. -/
theorem sum_swap_succ {M : Type*} [AddCommGroup M] {k : ℕ} (f : Fin (k + 1) → M) :
    ∑ p, ∑ i : Fin k, f (swap 0 p i.succ) = k • ∑ q, f q := by
  have h : ∀ p, ∑ i : Fin k, f (swap 0 p i.succ) = ∑ q, f q - f p := fun p => by
    rw [eq_sub_iff_add_eq, ← Equiv.sum_comp (swap 0 p) f, Fin.sum_univ_succ, swap_apply_left]
    abel
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, succ_nsmul]
  abel

omit [Fintype S] [DecidableEq S] in
/-- **The contraction**: under the alternation, the commutator terms of `capP_cons` add up to minus the diagonal
shift `k·[r p = b]` (`alt_update`, `alt_swap_update`, `sum_swap_succ`). -/
theorem alt_contract {k : ℕ} (Q : (Fin k → I) → R) (r : Fin (k + 1) → I) (b : I) :
    ∑ p, (Perm.sign (swap 0 p) : ℤ) •
        alt (fun w => ∑ j, if w j = b then Q (Function.update w j (r p)) else 0) (fun y => r (swap 0 p y.succ)) =
      -∑ p, (Perm.sign (swap 0 p) : ℤ) •
        ((if r p = b then (k : R) else 0) * alt Q fun y => r (swap 0 p y.succ)) := by
  set G : Fin (k + 1) → R := fun q =>
    if r q = b then (Perm.sign (swap 0 q) : ℤ) • alt Q (fun y => r (swap 0 q y.succ)) else 0 with hG
  have hl : ∀ p, (Perm.sign (swap 0 p) : ℤ) •
      alt (fun w => ∑ j, if w j = b then Q (Function.update w j (r p)) else 0) (fun y => r (swap 0 p y.succ)) =
      -∑ i : Fin k, G (swap 0 p i.succ) := fun p => by
    rw [alt_update, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [alt_swap_update, hG]
    dsimp only
    split_ifs
    · rw [smul_smul, mul_neg, ← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul, neg_smul]
    · simp
  have hr : ∀ p, (Perm.sign (swap 0 p) : ℤ) •
      ((if r p = b then (k : R) else 0) * alt Q fun y => r (swap 0 p y.succ)) = k • G p := fun p => by
    rw [hG]
    dsimp only
    split_ifs
    · rw [smul_comm, nsmul_eq_mul]
    · simp
  simp only [hl, hr, Finset.sum_neg_distrib, sum_swap_succ G, ← Finset.smul_sum]

/-- **The Capelli identity**: in a ring with commuting `x_{a,t}` and `∂_{b,t}·x_{a,u} = x_{a,u}·∂_{b,t} + [a = b,
u = t]`, `alt (capL · g) r = alt (capP · g) r` for all row maps `r` and `g`. By induction on `k`, peeling the first
column: `capL_cons` and `capP_cons` agree up to the diagonal shift and the commutator terms, which cancel by
`alt_contract`. -/
theorem capelli (hxx : ∀ a s b t, Commute (x a s) (x b t))
    (hdx : ∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) :
    ∀ (k : ℕ) (r g : Fin k → I), alt (fun w => capL x d w g) r = alt (fun w => capP x d w g) r
  | 0, r, g => by
    have h : ∀ w : Fin 0 → I, capL x d w g = capP x d w g := fun w => by simp [capL, capP, xw]
    simp only [h]
  | k + 1, r, g => by
    obtain ⟨g0, g', rfl⟩ : ∃ g0 g', g = Fin.cons g0 g' := ⟨g 0, Fin.tail g, (Fin.cons_self_tail g).symm⟩
    have ih := capelli hxx hdx k
    have hP : ∀ (a : I) (w : Fin k → I), capP x d (Fin.cons a w) (Fin.cons g0 g') =
        polE x d a g0 * capP x d w g' - ∑ j, if w j = g0 then capP x d (Function.update w j a) g' else 0 :=
      fun a w => by rw [capP_cons x d hxx hdx]; abel
    rw [alt_succ, alt_succ]
    simp only [capL_cons, hP, alt_mul_left, alt_sub, ih]
    have hc := alt_contract (fun w => capP x d w g') r g0
    simp only [add_mul, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hc, sub_neg_eq_add]

end Capelli

/-! ## The Weyl algebra of a leading block -/

section Instance

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {K : Type} [Field K]

/-- **Multiplication by `x_{τ,t,i}`**, for the row `t` and the column `i` of the leading block of size `s + 1`. -/
noncomputable def xop (τ : Φ) (s : Fin n) (i t : Fin (s + 1)) : Module.End K (Pol Φ n K) :=
  LinearMap.mulLeft K (X (τ, Fin.castLE s.isLt t, Fin.castLE s.isLt i))

/-- **The derivative `∂_{τ,t,i}`**, for the row `t` and the column `i` of the leading block of size `s + 1`. -/
noncomputable def dop (τ : Φ) (s : Fin n) (i t : Fin (s + 1)) : Module.End K (Pol Φ n K) :=
  (pderiv (τ, Fin.castLE s.isLt t, Fin.castLE s.isLt i)).toLinearMap

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The multiplications commute.** -/
theorem xop_comm (τ : Φ) (s : Fin n) (a u b t : Fin (s + 1)) :
    Commute (xop (K := K) τ s a u) (xop τ s b t) :=
  LinearMap.ext fun p => by simp [xop, mul_left_comm]

omit [Fintype Φ] in
/-- **The canonical commutation relation** `∂_{b,t}·x_{a,u} = x_{a,u}·∂_{b,t} + [a = b, u = t]`. -/
theorem dop_xop (τ : Φ) (s : Fin n) (a u b t : Fin (s + 1)) :
    dop (K := K) τ s b t * xop τ s a u = xop τ s a u * dop τ s b t + if a = b ∧ u = t then 1 else 0 := by
  refine LinearMap.ext fun p => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, xop, dop, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    pderiv_mul, pderiv_X]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [add_comm]
  · have hne : (τ, Fin.castLE s.isLt t, Fin.castLE s.isLt b) ≠ (τ, Fin.castLE s.isLt u, Fin.castLE s.isLt a) :=
      fun h' => h (by simp only [Prod.mk.injEq, Fin.castLE_inj, true_and] at h'; exact ⟨h'.2.symm, h'.1.symm⟩)
    simp [hne]

/-- **A triangular product of operators**: if `T_j F = λ_j F` when `p j`, and `T_j F = 0` when `¬p j` and `p` holds
past `j`, then `(T_0⋯T_{k−1}) F = (∏ λ)·F` if `p` holds everywhere, and `0` otherwise. -/
theorem ofFn_prod_apply {M : Type*} [AddCommGroup M] [Module K M] (F : M) :
    ∀ {k : ℕ} (T : Fin k → Module.End K M) (p : Fin k → Prop) [DecidablePred p] (lam : Fin k → K),
      (∀ j, p j → T j F = lam j • F) → (∀ j, ¬ p j → (∀ j', j < j' → p j') → T j F = 0) →
      (List.ofFn T).prod F = (if ∀ j, p j then ∏ j, lam j else 0) • F
  | 0, T, p, _, lam, _, _ => by simp
  | k + 1, T, p, _, lam, h1, h2 => by
    have h2' : ∀ j : Fin k, ¬ p j.succ → (∀ j', j < j' → p j'.succ) → T j.succ F = 0 := fun j hj hj' =>
      h2 _ hj fun j'' hj'' => by
        cases j'' using Fin.cases with
        | zero => exact absurd hj'' (Fin.not_lt_zero _)
        | succ j' => exact hj' j' (Fin.succ_lt_succ_iff.1 hj'')
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ofFn_prod_apply F (fun j => T j.succ) (fun j => p j.succ) (fun j => lam j.succ) (fun j hj => h1 _ hj) h2']
    by_cases hall : ∀ j : Fin k, p j.succ
    · rw [ite_eq_left hall, map_smul]
      by_cases h0 : p 0
      · rw [h1 0 h0, smul_smul, ite_eq_left (Fin.forall_fin_succ.2 ⟨h0, hall⟩), Fin.prod_univ_succ, mul_comm]
      · have hk : T 0 F = 0 := h2 0 h0 fun j' hj' => by
          cases j' using Fin.cases with
          | zero => exact absurd hj' (lt_irrefl _)
          | succ j => exact hall j
        rw [hk, smul_zero, ite_eq_right (fun h => h0 (h 0)), zero_smul]
    · rw [ite_eq_right hall, zero_smul, map_zero, ite_eq_right (fun h => hall fun j => h _), zero_smul]

omit [Fintype Φ] in
/-- **The Euler term of one variable**: the coefficient of `x^m` in `x_v·∂_v F` is `m_v·F_m`. -/
theorem coeff_X_mul_pderiv (F : Pol Φ n K) (v : Φ × Fin n × Fin n) (m : Φ × Fin n × Fin n →₀ ℕ) :
    (X v * pderiv v F).coeff m = (m v : K) * F.coeff m := by
  rw [coeff_X_mul']
  split_ifs with h
  · have hv : m v ≠ 0 := Finsupp.mem_support_iff.1 h
    rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hv, mul_comm]
    congr 1
    have : (m - Finsupp.single v 1 : Φ × Fin n × Fin n →₀ ℕ) v + 1 = m v := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      omega
    rw [← this, Nat.cast_succ]
  · rw [Finsupp.notMem_support_iff.1 h]
    simp

/-- **Euler's identity for a column**: `Σ_a x_{τ,a,b}·∂_{τ,a,b} F = ν_{τ,b}·F` for `F` of column weight `ν`. -/
theorem euler_col {F : Pol Φ n K} {ν : Φ → Fin n → ℕ} (hF : IsWeightedHomogeneous (colW Φ n) F ν) (τ : Φ)
    (b : Fin n) : ∑ a, X (τ, a, b) * pderiv (τ, a, b) F = C (ν τ b : K) * F := by
  ext m
  rw [coeff_sum, coeff_C_mul]
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul]
  by_cases h : F.coeff m = 0
  · rw [h, mul_zero, mul_zero]
  · congr 1
    rw [← hF h, weight_colW_apply]
    push_cast
    rfl

/-- **Rows of weight zero do not occur**: `∂_{τ,a,b} F = 0` for `F` of row weight `ν` with `ν_{τ,a} = 0`. -/
theorem pderiv_eq_zero_of_row {F : Pol Φ n K} {ν : Φ → Fin n → ℕ} (hF : IsWeightedHomogeneous (rowW Φ n) F ν)
    {τ : Φ} {a : Fin n} (ha : ν τ a = 0) (b : Fin n) : pderiv (τ, a, b) F = 0 := by
  ext m
  rw [coeff_pderiv]
  by_cases h : F.coeff (m + Finsupp.single (τ, a, b) 1) = 0
  · simp [h]
  · have hw := congrFun (congrFun (hF h) τ) a
    rw [weight_rowW_apply, ha] at hw
    have hb := Finset.sum_eq_zero_iff.1 hw b (Finset.mem_univ _)
    simp at hb

/-- **The polarisations of the leading block**: if the rows past `s` have weight zero, the sum over the rows of the
leading block is the full polarisation. -/
theorem sum_rows {F : Pol Φ n K} {ν : Φ → Fin n → ℕ} (hF : IsWeightedHomogeneous (rowW Φ n) F ν) {τ : Φ}
    {s : Fin n} (hz : ∀ a, s < a → ν τ a = 0) (k j : Fin n) :
    ∑ t : Fin (s + 1), X (τ, Fin.castLE s.isLt t, k) * pderiv (τ, Fin.castLE s.isLt t, j) F =
      ∑ a, X (τ, a, k) * pderiv (τ, a, j) F := by
  refine ((Finset.sum_map Finset.univ (Fin.castLEEmb s.isLt)
    (fun a => X (τ, a, k) * pderiv (τ, a, j) F)).symm.trans ?_)
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
  have has : s < a := by
    by_contra h
    exact ha (Finset.mem_map.2 ⟨⟨a, by rw [Fin.not_lt] at h; exact Nat.lt_succ_of_le h⟩, Finset.mem_univ _, rfl⟩)
  rw [pderiv_eq_zero_of_row hF (hz a has), mul_zero]

end Instance

/-! ## The Capelli identity at the highest weight vector -/

section Step

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {K : Type} [Field K]

/-- **The dual minor** `D_{τ,s}(∂) = Σ_π sign(π)·∏_j ∂_{τ,π j,j}`, Fock-adjoint to the leading minor
(`fock_minor_left`). -/
noncomputable def dDet (τ : Φ) (s : Fin n) : Module.End K (Pol Φ n K) :=
  ∑ π : Perm (Fin (s + 1)), (Perm.sign π : ℤ) • xw (dop τ s) id ⇑π

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A word of multiplications** is the multiplication by the monomial. -/
theorem xw_xop (τ : Φ) (s : Fin n) : ∀ {k : ℕ} (w t : Fin k → Fin (s + 1)),
    xw (xop (K := K) τ s) w t =
      LinearMap.mulLeft K (∏ j, X (τ, Fin.castLE s.isLt (t j), Fin.castLE s.isLt (w j)))
  | 0, w, t => by simp [xw]; rfl
  | k + 1, w, t => by
    have h : xw (xop (K := K) τ s) w t =
        xop τ s (w 0) (t 0) * xw (xop τ s) (fun j => w j.succ) fun j => t j.succ := by
      simp [xw, List.ofFn_succ]
    rw [h, xw_xop τ s, Fin.prod_univ_succ, LinearMap.mulLeft_mul, xop]
    rfl

omit [Fintype Φ] [DecidableEq Φ] in
/-- **Alternating the columns of a monomial word** gives the minor on the rows `t`. -/
theorem alt_xop (τ : Φ) (s : Fin n) (t : Fin (s + 1) → Fin (s + 1)) :
    ∑ σ : Perm (Fin (s + 1)), (Perm.sign σ : ℤ) •
      ∏ j, (X (τ, Fin.castLE s.isLt (t j), Fin.castLE s.isLt (σ j)) : Pol Φ n K) =
      minor τ s (Fin.castLE s.isLt ∘ t) := by
  rw [minor, ← Matrix.det_transpose, Matrix.det_apply]
  simp [xMat, Units.smul_def]

/-- **A sum over the self-maps of `Fin k`** that vanishes on the non-injective ones is a sum over permutations. -/
theorem sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] {k : ℕ} (φ : (Fin k → Fin k) → M)
    (h : ∀ f, ¬ Function.Injective f → φ f = 0) : ∑ f, φ f = ∑ σ : Perm (Fin k), φ σ := by
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) fun f _ hf => by_contra fun hi => hf (h f hi)]
  symm
  refine Finset.sum_bij' (fun σ _ => ⇑σ) (fun f hf => Equiv.ofBijective f
    (Finite.injective_iff_bijective.1 (Finset.mem_filter.1 hf).2)) (fun σ _ => Finset.mem_filter.2
      ⟨Finset.mem_univ _, σ.injective⟩) (fun _ _ => Finset.mem_univ _) (fun σ _ => Equiv.ext fun _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- **The last point a permutation moves goes down**: if `σ` fixes everything past `j` but not `j`, then
`σ j < j`. -/
theorem perm_lt_of_fixed {k : ℕ} (σ : Perm (Fin k)) {j : Fin k} (hj : σ j ≠ j) (h : ∀ j', j < j' → σ j' = j') :
    σ j < j := by
  by_contra hlt
  exact hj (σ.injective (h (σ j) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hj))))

omit [Fintype Φ] [DecidableEq Φ] in
/-- **The polarisation of the leading block**, applied. -/
theorem polE_apply (τ : Φ) (s : Fin n) (a b : Fin (s + 1)) (F : Pol Φ n K) :
    polE (xop τ s) (dop τ s) a b F = ∑ t : Fin (s + 1), X (τ, Fin.castLE s.isLt t, Fin.castLE s.isLt a) *
      pderiv (τ, Fin.castLE s.isLt t, Fin.castLE s.isLt b) F := by
  simp [polE, xop, dop, LinearMap.sum_apply]

/-- **Capelli at the highest weight vector**: if the rows of block `τ` past `s` have weight zero,
`D_{τ,s}·D_{τ,s}(∂) hw_ν = ∏_{j ≤ s} (ν_{τ,j} + s − j)·hw_ν`. In the Capelli identity for the leading block, the left
side is `D·D(∂)` (`alt_xop`, `sum_fun_eq_sum_perm`), and on the right only `σ = 1` survives (`ofFn_prod_apply`):
the raising polarisations kill `hw_ν` (`polar_eq_zero`) and the diagonal ones are its column degrees (`euler_col`). -/
theorem capelli_hw [CharZero K] {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) (τ : Φ) (s : Fin n)
    (hz : ∀ a, s < a → ν τ a = 0) :
    minor τ s (Fin.castLE s.isLt) * dDet τ s (hw K ν) =
      C (∏ j : Fin (s + 1), ((ν τ (Fin.castLE s.isLt j) + (s - j) : ℕ) : K)) * hw K ν := by
  set F := hw K ν with hF
  have hC := LinearMap.congr_fun (capelli (xop (K := K) τ s) (dop τ s) (xop_comm τ s) (dop_xop τ s) (s + 1) id id) F
  have hrow : IsWeightedHomogeneous (rowW Φ n) F ν := hw_isWH_row hν
  have hcol : IsWeightedHomogeneous (colW Φ n) F ν := (mem_nabla_iff.1 (hw_mem_nabla hν)).1
  set lam : Fin (s + 1) → K := fun j => ((ν τ (Fin.castLE s.isLt j) + (s - j) : ℕ) : K) with hlam
  have hT : ∀ σ : Perm (Fin (s + 1)), capL (xop τ s) (dop τ s) (id ∘ ⇑σ) id F =
      (if ∀ j, σ j = j then ∏ j, lam j else 0) • F := fun σ => by
    refine ofFn_prod_apply F _ (fun j => σ j = j) lam (fun j hj => ?_) fun j hj hj' => ?_
    · simp only [Function.comp_apply, id_eq, hj, ↓reduceIte, LinearMap.add_apply, polE_apply,
        Module.End.natCast_apply, sum_rows hrow hz, euler_col hcol, hlam]
      rw [← smul_eq_C_mul, ← Nat.cast_smul_eq_nsmul K, ← add_smul]
      push_cast
      rfl
    · have hlt := perm_lt_of_fixed σ hj hj'
      change ((polE (xop τ s) (dop τ s) (σ j) j + if σ j = j then (((s + 1) - 1 - j : ℕ) :
        Module.End K (Pol Φ n K)) else 0 : Module.End K (Pol Φ n K)) F) = 0
      rw [LinearMap.add_apply, ite_eq_right hj, LinearMap.zero_apply, add_zero, polE_apply, sum_rows hrow hz]
      exact polar_eq_zero (hw_mem_nabla hν) τ
        (Fin.lt_def.2 (by simpa only [Fin.val_castLE] using Fin.lt_def.1 hlt))
  have hL : (alt (fun w => capL (xop τ s) (dop τ s) w id) id) F = (∏ j, lam j) • F := by
    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, hT]
    rw [Finset.sum_eq_single 1 (fun σ _ hσ => by
      rw [ite_eq_right (show ¬ ∀ j, σ j = j from fun h => hσ (Equiv.ext h)), zero_smul, smul_zero]) (by simp)]
    simp
  have hR : (alt (fun w => capP (xop τ s) (dop τ s) w id) id) F =
      minor τ s (Fin.castLE s.isLt) * dDet τ s F := by
    simp only [alt, capP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, Finset.smul_sum,
      xw_xop, LinearMap.mulLeft_apply]
    rw [Finset.sum_comm]
    have h1 : ∀ t : Fin (s + 1) → Fin (s + 1), ∑ σ : Perm (Fin (s + 1)), (Perm.sign σ : ℤ) •
        ((∏ j, X (τ, Fin.castLE s.isLt (t j), Fin.castLE s.isLt ((id ∘ ⇑σ) j))) * xw (dop τ s) id t F) =
        minor τ s (Fin.castLE s.isLt ∘ t) * xw (dop τ s) id t F := fun t => by
      rw [← alt_xop, Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => (smul_mul_assoc _ _ _).symm
    simp only [h1]
    rw [sum_fun_eq_sum_perm _ fun t ht => by
      rw [minor_eq_zero (I := Fin.castLE s.isLt ∘ t) fun h => ht h.of_comp, zero_mul]]
    simp only [minor_comp_perm, dDet, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum, mul_assoc]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [zsmul_eq_mul, mul_left_comm]
  rw [hL, hR] at hC
  rw [← hC, smul_eq_C_mul]

end Step

/-! ## The recursion `κ(ν) = ∏_{j ≤ s} (ν_{τ,j} + s − j)·κ(ν − ω_s)` -/

section Peel

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {K : Type} [Field K]

omit [DecidableEq Φ] in
/-- **Multiplication by a monomial is adjoint to the derivatives**: `⟨(∏_j x_{v j})·G, H⟩ = ⟨G, ∂_{v 0}⋯∂_{v (k−1)} H⟩`
(`fock_mul_X`). -/
theorem fock_prod_X : ∀ {k : ℕ} (v : Fin k → Φ × Fin n × Fin n) (G H : Pol Φ n K),
    fockWith (RingHom.id K) ((∏ j, X (v j)) * G) H =
      fockWith (RingHom.id K) G ((List.ofFn fun j => (pderiv (v j)).toLinearMap).prod H)
  | 0, v, G, H => by simp
  | k + 1, v, G, H => by
    rw [Fin.prod_univ_castSucc, List.ofFn_succ', List.prod_concat, Module.End.mul_apply,
      show (∏ j : Fin k, X (v j.castSucc)) * X (v (Fin.last k)) * G = (∏ j : Fin k, X (v j.castSucc)) * G *
        X (v (Fin.last k)) by ring, fock_mul_X, fock_prod_X]
    rfl

omit [DecidableEq Φ] in
/-- **Multiplication by a leading minor is adjoint to the dual minor**: `⟨D_{τ,s}·G, H⟩ = ⟨G, D_{τ,s}(∂) H⟩`. -/
theorem fock_minor_left (τ : Φ) (s : Fin n) (G H : Pol Φ n K) :
    fockWith (RingHom.id K) (minor τ s (Fin.castLE s.isLt) * G) H = fockWith (RingHom.id K) G (dDet τ s H) := by
  rw [minor_eq_sum, Finset.sum_mul, fock_sum_left, dDet, LinearMap.sum_apply, fock_sum_right]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [mul_assoc, ← map_intCast (C : K →+* Pol Φ n K), fock_C_mul_left, fock_prod_X, LinearMap.smul_apply,
    zsmul_eq_mul, ← map_intCast (C : K →+* Pol Φ n K), fock_C_mul_right]
  rfl

omit [Fintype Φ] [DecidableEq Φ] in
/-- **A leading minor is nonzero**: it is `1` at the identity. -/
theorem minor_ne_zero (τ : Φ) (s : Fin n) : (minor τ s (Fin.castLE s.isLt) : Pol Φ n K) ≠ 0 := fun h => by
  have := eval_one_minor (L := K) τ s
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- **The multiplicities after removing a column**: if `μ` is antitone, `μ_s > 0` and `μ` vanishes past `s`, then
`mult μ = mult (μ − 1) + [· = s]`. -/
theorem mult_peel {μ : Fin n → ℕ} (hμ : Antitone μ) {s : Fin n} (hs : 0 < μ s) (hz : ∀ a, s < a → μ a = 0)
    (t : Fin n) : mult μ t = mult (fun b => μ b - 1) t + if t = s then 1 else 0 := by
  unfold mult
  beta_reduce
  rcases lt_trichotomy t s with h | rfl | h
  · have hh : (t : ℕ) + 1 < n := by have := s.isLt; rw [Fin.lt_def] at h; omega
    have h1 : μ s ≤ μ ⟨t + 1, hh⟩ := hμ (Fin.le_def.2 (by rw [Fin.lt_def] at h; simp; omega))
    have h2 : μ ⟨t + 1, hh⟩ ≤ μ t := hμ (Fin.le_def.2 (by simp))
    simp only [hh, ↓reduceDIte, h.ne, ↓reduceIte]
    omega
  · simp only [↓reduceIte]
    split_ifs with hh
    · have := hz ⟨t + 1, hh⟩ (Fin.lt_def.2 (by simp))
      omega
    · omega
  · have h0 := hz t h
    simp only [h.ne', ↓reduceIte]
    split_ifs with hh
    · have := hz ⟨t + 1, hh⟩ (Fin.lt_def.2 (by rw [Fin.lt_def] at h; simp; omega))
      omega
    · omega

/-- **Removing a column from the highest weight vector**: `hw_ν = D_{τ,s}·hw_ν'`, `ν'_{τ,b} = ν_{τ,b} − 1`, when
`ν_{τ,s} > 0` and block `τ` vanishes past `s`. -/
theorem hw_peel {ν : Φ → Fin n → ℕ} {τ : Φ} (hν : Antitone (ν τ)) {s : Fin n} (hs : 0 < ν τ s)
    (hz : ∀ a, s < a → ν τ a = 0) :
    hw K ν = minor τ s (Fin.castLE s.isLt) * hw K (Function.update ν τ fun b => ν τ b - 1) := by
  classical
  have hσ : ∀ σ, (∏ t : Fin n, (minor σ t (Fin.castLE t.isLt) : Pol Φ n K) ^ mult (ν σ) t) =
      (if σ = τ then minor τ s (Fin.castLE s.isLt) else 1) *
        ∏ t : Fin n, minor σ t (Fin.castLE t.isLt) ^ mult (Function.update ν τ (fun b => ν τ b - 1) σ) t := by
    intro σ
    by_cases h : σ = τ
    · subst h
      simp only [Function.update_self, ↓reduceIte, mult_peel hν hs hz, pow_add, Finset.prod_mul_distrib,
        pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', Finset.mem_univ]
      ring
    · simp [h]
  simp only [hw, hσ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- **The recursion**: `κ(ν) = ∏_{j ≤ s} (ν_{τ,j} + s − j)·κ(ν')`, `ν'_{τ,b} = ν_{τ,b} − 1`, when `ν_{τ,s} > 0` and
block `τ` vanishes past `s`. With `hw_ν = D·hw_ν'` (`hw_peel`), `κ(ν) = ⟨hw_ν', D(∂) hw_ν⟩` (`fock_minor_left`), and
`D(∂) hw_ν = c·hw_ν'` by `capelli_hw`, cancelling `D ≠ 0`. -/
theorem fock_hw_peel [CharZero K] {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) {τ : Φ} {s : Fin n}
    (hs : 0 < ν τ s) (hz : ∀ a, s < a → ν τ a = 0) :
    fockWith (RingHom.id K) (hw K ν) (hw K ν) =
      (∏ j : Fin (s + 1), ((ν τ (Fin.castLE s.isLt j) + (s - j) : ℕ) : K)) *
        fockWith (RingHom.id K) (hw K (Function.update ν τ fun b => ν τ b - 1))
          (hw K (Function.update ν τ fun b => ν τ b - 1)) := by
  set c := ∏ j : Fin (s + 1), ((ν τ (Fin.castLE s.isLt j) + (s - j) : ℕ) : K)
  set ν' := Function.update ν τ fun b => ν τ b - 1
  have hfac : hw K ν = minor τ s (Fin.castLE s.isLt) * hw K ν' := hw_peel (hν τ) hs hz
  have hD : dDet τ s (hw K ν) = C c * hw K ν' := by
    refine mul_left_cancel₀ (minor_ne_zero τ s) ?_
    rw [capelli_hw hν τ s hz, hfac]
    ring
  conv_lhs => arg 2; rw [hfac]
  rw [fock_minor_left, hD, fock_C_mul_right]

end Peel

/-! ## The product formula -/

section Formula

/-- **The row factor** `μ_i!·∏_{j>i} (μ_i + j − i)/(μ_i − μ_j + j − i)`; `κ` is the product of the row factors
(`fock_hw_eq_prod`). -/
noncomputable def rowF {n : ℕ} (μ : Fin n → ℕ) (i : Fin n) : ℚ :=
  ((μ i).factorial : ℚ) *
    ∏ j ∈ Finset.Ioi i, ((μ i + (j.val - i.val) : ℕ) : ℚ) / ((μ i - μ j + (j.val - i.val) : ℕ) : ℚ)

/-- **A rising product of factorial type**: `a!·∏_{i < m ≤ i + L} (a + m − i) = (a + L)!`. -/
theorem factorial_mul_prod_Ioc (a i : ℕ) : ∀ L : ℕ,
    a.factorial * ∏ m ∈ Finset.Ioc i (i + L), (a + (m - i)) = (a + L).factorial
  | 0 => by simp
  | L + 1 => by
    rw [← add_assoc, Finset.prod_Ioc_succ_top (by omega), ← mul_assoc, factorial_mul_prod_Ioc a i L,
      show i + L + 1 - i = L + 1 by omega, ← add_assoc, Nat.factorial_succ, mul_comm]

/-- **The same over `Fin n`**: `a!·∏_{i < j ≤ s} (a + j − i) = (a + s − i)!` for `i ≤ s`. -/
theorem factorial_mul_prod_fin {n : ℕ} (a : ℕ) {i s : Fin n} (hi : i ≤ s) :
    a.factorial * ∏ j ∈ Finset.Ioc i s, (a + (j.val - i.val)) = (a + (s.val - i.val)).factorial := by
  have h : ∏ j ∈ Finset.Ioc i s, (a + (j.val - i.val)) =
      ∏ m ∈ Finset.Ioc i.val s.val, (a + (m - i.val)) := by
    rw [← Fin.map_valEmbedding_Ioc, Finset.prod_map]
    rfl
  rw [h, show s.val = i.val + (s.val - i.val) by rw [Fin.le_def] at hi; omega, factorial_mul_prod_Ioc]
  congr 2
  omega

/-- **The rows past `s` do not change** when a column is removed from a shape that vanishes past `s`. -/
theorem rowF_hi {n : ℕ} {μ : Fin n → ℕ} {s : Fin n} (hz : ∀ a, s < a → μ a = 0) {i : Fin n} (hi : s < i) :
    rowF μ i = rowF (fun b => μ b - 1) i := by
  have h0 : ∀ j, i ≤ j → μ j - 1 = μ j := fun j hj => by rw [hz j (lt_of_lt_of_le hi hj)]
  unfold rowF
  beta_reduce
  rw [h0 i le_rfl]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [h0 j (le_of_lt (Finset.mem_Ioi.1 hj))]

/-- **A row up to `s` gains the factor `μ_i + s − i`** when a column is added: the factors with `j > s` are `1`, the
denominators with `j ≤ s` do not change, and the numerators telescope to `(μ_i + s − i)!/(μ_i − 1 + s − i)!`
(`factorial_mul_prod_fin`). -/
theorem rowF_lo {n : ℕ} {μ : Fin n → ℕ} (hμ : Antitone μ) {s : Fin n} (hs : 0 < μ s) (hz : ∀ a, s < a → μ a = 0)
    {i : Fin n} (hi : i ≤ s) :
    rowF μ i = ((μ i + (s.val - i.val) : ℕ) : ℚ) * rowF (fun b => μ b - 1) i := by
  have ha : 1 ≤ μ i := le_trans hs (hμ hi)
  have hsplit : ∀ f : Fin n → ℚ, ∏ j ∈ Finset.Ioi i, f j =
      (∏ j ∈ Finset.Ioc i s, f j) * ∏ j ∈ (Finset.Ioi i).filter (fun j => ¬ j ≤ s), f j := fun f => by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ioi i) (· ≤ s)]
    congr 2
    ext j
    simp [Finset.mem_Ioc]
  have hhi : ∀ j ∈ (Finset.Ioi i).filter (fun j => ¬ j ≤ s), μ j = 0 := fun j hj =>
    hz j (not_le.1 (Finset.mem_filter.1 hj).2)
  have hpos : ∀ j ∈ (Finset.Ioi i).filter (fun j => ¬ j ≤ s), 0 < j.val - i.val := fun j hj => by
    have := Finset.mem_Ioi.1 (Finset.mem_filter.1 hj).1
    rw [Fin.lt_def] at this
    omega
  have hone : ∏ j ∈ (Finset.Ioi i).filter (fun j => ¬ j ≤ s),
      ((μ i + (j.val - i.val) : ℕ) : ℚ) / ((μ i - μ j + (j.val - i.val) : ℕ) : ℚ) = 1 :=
    Finset.prod_eq_one fun j hj => by
      rw [hhi j hj, Nat.sub_zero, div_self]
      have := hpos j hj
      positivity
  have hone' : ∏ j ∈ (Finset.Ioi i).filter (fun j => ¬ j ≤ s),
      ((μ i - 1 + (j.val - i.val) : ℕ) : ℚ) / ((μ i - 1 - (μ j - 1) + (j.val - i.val) : ℕ) : ℚ) = 1 :=
    Finset.prod_eq_one fun j hj => by
      rw [hhi j hj, Nat.zero_sub, Nat.sub_zero, div_self]
      have := hpos j hj
      positivity
  have hden : ∀ j ∈ Finset.Ioc i s, μ i - 1 - (μ j - 1) = μ i - μ j := fun j hj => by
    have : 1 ≤ μ j := le_trans hs (hμ (Finset.mem_Ioc.1 hj).2)
    omega
  have hA : ((μ i).factorial : ℚ) * ∏ j ∈ Finset.Ioc i s, ((μ i + (j.val - i.val) : ℕ) : ℚ) =
      ((μ i + (s.val - i.val)).factorial : ℚ) := by
    exact_mod_cast factorial_mul_prod_fin (μ i) hi
  have hA' : ((μ i - 1).factorial : ℚ) * ∏ j ∈ Finset.Ioc i s, ((μ i - 1 + (j.val - i.val) : ℕ) : ℚ) =
      ((μ i - 1 + (s.val - i.val)).factorial : ℚ) := by
    exact_mod_cast factorial_mul_prod_fin (μ i - 1) hi
  have hfac : ((μ i + (s.val - i.val)).factorial : ℚ) =
      ((μ i + (s.val - i.val) : ℕ) : ℚ) * ((μ i - 1 + (s.val - i.val)).factorial : ℚ) := by
    rw [show μ i + (s.val - i.val) = (μ i - 1 + (s.val - i.val)) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  set D := ∏ j ∈ Finset.Ioc i s, ((μ i - μ j + (j.val - i.val) : ℕ) : ℚ)
  have hL : rowF μ i = ((μ i + (s.val - i.val)).factorial : ℚ) / D := by
    unfold rowF
    rw [hsplit, hone, mul_one, Finset.prod_div_distrib, ← mul_div_assoc, hA]
  have hR : rowF (fun b => μ b - 1) i = ((μ i - 1 + (s.val - i.val)).factorial : ℚ) / D := by
    unfold rowF
    beta_reduce
    have hprod : ∏ j ∈ Finset.Ioc i s,
        ((μ i - 1 + (j.val - i.val) : ℕ) : ℚ) / ((μ i - 1 - (μ j - 1) + (j.val - i.val) : ℕ) : ℚ) =
        ∏ j ∈ Finset.Ioc i s, ((μ i - 1 + (j.val - i.val) : ℕ) : ℚ) / ((μ i - μ j + (j.val - i.val) : ℕ) : ℚ) :=
      Finset.prod_congr rfl fun j hj => by rw [hden j hj]
    rw [hsplit, hone', mul_one, hprod, Finset.prod_div_distrib, ← mul_div_assoc, hA']
  rw [hL, hR, hfac, mul_div_assoc]

/-- **The product of the row factors** gains `∏_{j ≤ s} (μ_j + s − j)` when a column is added to a shape that
vanishes past `s` (`rowF_lo`, `rowF_hi`). -/
theorem prod_rowF_peel {n : ℕ} {μ : Fin n → ℕ} (hμ : Antitone μ) {s : Fin n} (hs : 0 < μ s)
    (hz : ∀ a, s < a → μ a = 0) :
    ∏ i, rowF μ i = (∏ j : Fin (s + 1), ((μ (Fin.castLE s.isLt j) + (s - j) : ℕ) : ℚ)) *
      ∏ i, rowF (fun b => μ b - 1) i := by
  have h : ∀ i, rowF μ i =
      (if i ≤ s then ((μ i + (s.val - i.val) : ℕ) : ℚ) else 1) * rowF (fun b => μ b - 1) i := fun i => by
    split_ifs with hi
    · exact rowF_lo hμ hs hz hi
    · rw [one_mul]
      exact rowF_hi hz (not_le.1 hi)
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, ← Finset.prod_filter]
  congr 1
  have hmap : Finset.univ.filter (fun i : Fin n => i ≤ s) = Finset.univ.map (Fin.castLEEmb s.isLt) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.coe_castLEEmb]
    constructor
    · intro hi
      exact ⟨⟨i, Nat.lt_succ_of_le (Fin.le_def.1 hi)⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      exact Fin.le_def.2 (by simp [Nat.le_of_lt_succ j.isLt])
  rw [hmap, Finset.prod_map]
  rfl

/-- **The Fock norm of `hw_ν` is the product of the row factors**, `κ(ν) = ∏_τ ∏_i rowF(ν_τ, i)`, by induction on
`|ν|`: remove a column from the last nonzero row `s` of a nonzero block (`fock_hw_peel`, `prod_rowF_peel`). -/
theorem fock_hw_eq_prod {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} :
    ∀ (N : ℕ) (ν : Φ → Fin n → ℕ), ∑ σ, ∑ b, ν σ b = N → (∀ σ, Antitone (ν σ)) →
      fockWith (RingHom.id ℚ) (hw ℚ ν) (hw ℚ ν) = ∏ σ, ∏ i, rowF (ν σ) i := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ν hN hν
  by_cases h0 : ∀ σ b, ν σ b = 0
  · have hhw : hw ℚ ν = 1 := by simp [hw, mult, h0]
    have hrow : ∀ σ i, rowF (ν σ) i = 1 := fun σ i => by
      unfold rowF
      simp only [h0, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero, zero_add]
      refine Finset.prod_eq_one fun j hj => div_self ?_
      have := Finset.mem_Ioi.1 hj
      rw [Fin.lt_def] at this
      have : 0 < j.val - i.val := by omega
      positivity
    rw [hhw, ← C_1, fock_C]
    simp [hrow]
  push Not at h0
  obtain ⟨τ, b, hb⟩ := h0
  set S := Finset.univ.filter fun b => 0 < ν τ b with hS
  have hne : S.Nonempty := ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hb⟩⟩
  set s := S.max' hne
  have hs : 0 < ν τ s := (Finset.mem_filter.1 (S.max'_mem hne)).2
  have hz : ∀ a, s < a → ν τ a = 0 := fun a ha => by
    by_contra h
    exact absurd (S.le_max' a (Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩)) (not_le.2 ha)
  set ν' := Function.update ν τ fun b => ν τ b - 1 with hν'
  have hν'σ : ∀ σ, ν' σ = if σ = τ then fun b => ν τ b - 1 else ν σ := fun σ => by
    by_cases h : σ = τ
    · subst h; simp [hν']
    · simp [hν', h]
  have hant : ∀ σ, Antitone (ν' σ) := fun σ => by
    rw [hν'σ]
    split_ifs
    · exact fun a b hab => Nat.sub_le_sub_right (hν τ hab) 1
    · exact hν σ
  have hlt : ∑ σ, ∑ b, ν' σ b < N := by
    rw [← hN]
    refine Finset.sum_lt_sum (fun σ _ => Finset.sum_le_sum fun b _ => ?_) ⟨τ, Finset.mem_univ _, ?_⟩
    · rw [hν'σ]
      split_ifs with h
      · subst h
        exact Nat.sub_le (ν σ b) 1
      · exact le_rfl
    · rw [hν'σ, ite_eq_left rfl]
      exact Finset.sum_lt_sum (fun b _ => Nat.sub_le _ _) ⟨s, Finset.mem_univ _, by omega⟩
  rw [fock_hw_peel hν hs hz, ih _ hlt ν' rfl hant]
  have hσ : ∀ σ, ∏ i, rowF (ν σ) i = (if σ = τ then ∏ j : Fin (s + 1),
      ((ν τ (Fin.castLE s.isLt j) + (s - j) : ℕ) : ℚ) else 1) * ∏ i, rowF (ν' σ) i := fun σ => by
    rw [hν'σ]
    split_ifs with h
    · subst h
      exact prod_rowF_peel (hν σ) hs hz
    · rw [one_mul]
  rw [Finset.prod_congr rfl fun σ _ => hσ σ, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

end Formula

/-! ## The classical value of `κ`, and the sandwich exponent -/

section Main

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ}

/-- **The Fock norm of the highest weight vector** (main). For antitone `ν`, block by block,
`κ·∏_{i<j} (ν_i − ν_j + j − i) = ∏_b ν_b!·∏_{i<j} (ν_i + j − i)`, multiplied over the blocks: the hypothesis of
`WeylSandwich.sandExp_le`. From `fock_hw_eq_prod`. -/
theorem kapN_formula {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    kapN ν * ∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i - ν τ j + (j.val - i.val)) =
      (∏ τ, ∏ b, (ν τ b).factorial) * ∏ τ, ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (ν τ i + (j.val - i.val)) := by
  have hk := fock_hw_eq_prod _ ν rfl hν
  rw [← kapN_cast] at hk
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_mul, Nat.cast_prod, hk]
  have hrow : ∀ τ, ∏ i, rowF (ν τ) i = (∏ b, ((ν τ b).factorial : ℚ)) *
      (∏ i, ∏ j ∈ Finset.Ioi i, ((ν τ i + (j.val - i.val) : ℕ) : ℚ)) /
        ∏ i, ∏ j ∈ Finset.Ioi i, ((ν τ i - ν τ j + (j.val - i.val) : ℕ) : ℚ) := fun τ => by
    simp only [rowF, Finset.prod_mul_distrib, Finset.prod_div_distrib, mul_div_assoc]
  rw [Finset.prod_congr rfl fun τ _ => hrow τ, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    div_mul_cancel₀]
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have := Finset.mem_Ioi.1 hj
  rw [Fin.lt_def] at this
  have : 0 < j.val - i.val := by omega
  positivity

/-- **The sandwich exponent is logarithmic** (main): `WeylSandwich.sandExp_le` with its hypothesis discharged by
`kapN_formula`, for every antitone `ν`. -/
theorem sandExp_le' {p : ℕ} (hp : p.Prime) {ν : Φ → Fin n → ℕ} (hν : ∀ σ, Antitone (ν σ)) :
    sandExp p ν ≤ ∑ τ, (∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Nat.log p (ν τ i + (j.val - i.val)) +
      (n - 1) * ∑ b, Nat.log p (ν τ b)) :=
  sandExp_le hp (kapN_formula hν)

end Main

end FockNorm
