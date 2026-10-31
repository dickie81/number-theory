import ShortSieveCertChain
import ShortSieveCertDrop2

/-!
# The chain bound of a dropped node with two rough items

A node with two rough items has two chains of primes, one below each item's sifting prime: a role reversal starts them
(`p₂ > ⋯ > p_{k+2}` for `ρ`, and `p` for `β`), and Buchstab's steps on an item extend its chain. The constraints order
each chain: for consecutive primes `a > b`, one of them is `X_b − X_a < 0` in the items' forms (`chainOK`). The box's
primes that keep both orders have a sum at most the product of the two chains' sums
(`ShortSieveChain.sum_le_two_chains`).

* `formEq`: two forms agree, their coefficients up to trailing zeros (`val_eq_of_formEq`).
* `lt_of_linkOK`, `strictAnti_chT`: the constraints' order at the terms.
* `Sound.OK_of_drop2C`: **a dropped node with two rough items** has the loss `Ω_c Ω_g (hi_0 − lo_0)/DEN` times the
  product of any limit superiors of its two chain sums.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree ShortSieveChain SieveRough

open Classical

/-! ### Forms up to trailing zeros -/

/-- Two coefficient lists agree, the shorter padded with zeros. -/
def coeffEq : List ℤ → List ℤ → Bool
  | [], d => d.all fun b => b = 0
  | a :: c, [] => (a :: c).all fun b => b = 0
  | a :: c, b :: d => decide (a = b) && coeffEq c d

theorem dotR_eq_zero : ∀ (c : List ℤ), (c.all fun b => b = 0) = true → ∀ X, dotR c X = 0
  | [], _, _ => rfl
  | a :: c, h, X => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [dotR, h.1, dotR_eq_zero c h.2]
    simp

theorem dotR_eq_of_coeffEq : ∀ (c d : List ℤ), coeffEq c d = true → ∀ X, dotR c X = dotR d X
  | [], d, h, X => by rw [dotR_eq_zero d h]; rfl
  | a :: c, [], h, X => by rw [dotR_eq_zero (a :: c) h]; rfl
  | a :: c, b :: d, h, X => by
    simp only [coeffEq, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [dotR, dotR, h.1, dotR_eq_of_coeffEq c d h.2]

/-- Two forms agree, their coefficients up to trailing zeros. -/
def formEq (L M : LF) : Bool := decide (L.c0 = M.c0) && decide (L.ce = M.ce) && coeffEq L.c M.c

theorem val_eq_of_formEq {L M : LF} (h : formEq L M = true) (X : ℕ → ℝ) (H : ℝ) : L.val X H = M.val X H := by
  simp only [formEq, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold LF.val
  rw [h.1.1, h.1.2, dotR_eq_of_coeffEq _ _ h.2]

/-! ### The constraints' order of a chain -/

/-- The constraints order the primes `a > b`: one of them is `X_b − X_a < 0` in the items' forms. -/
def linkOK (Γ : List Con) (items : List LF) (a b : ℕ) : Bool :=
  Γ.any fun C => C.strict && formEq C.L ((items.getD b LF.zero).add ((items.getD a LF.zero).smul (-1)))

/-- The constraints order a chain's consecutive primes. -/
def chainOK (Γ : List Con) (items : List LF) : List ℕ → Bool
  | a :: b :: l => linkOK Γ items a b && chainOK Γ items (b :: l)
  | _ => true

theorem linkOK_of_chainOK {Γ : List Con} {items : List LF} : ∀ {c : List ℕ}, chainOK Γ items c = true →
    ∀ i, i + 1 < c.length → linkOK Γ items (c.getD i 0) (c.getD (i + 1) 0) = true
  | [], _, i, hi => by simp at hi
  | [_], _, i, hi => by simp at hi
  | a :: b :: l, h, i, hi => by
    simp only [chainOK, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := linkOK_of_chainOK h.2 i (by simp only [List.length_cons] at hi ⊢; omega)
      simpa using this

/-- **A linked pair is ordered** at the terms: `p_b < p_a`. -/
theorem lt_of_linkOK {K m : ℕ} {A : Rows K m} {items : List LF} (hI : ItemsOK A items) {Γ : List Con}
    {a b : Fin K} (hl : linkOK Γ items a b = true) {x : ℝ} (hx : 1 < x) {v : (Fin K → ℕ) × (Fin m → ℕ)}
    (hv : ∀ a, 0 < v.1 a) (hΓ : ∀ c ∈ Γ, c.Holds (coords A x v) (slack x v)) : v.1 b < v.1 a := by
  obtain ⟨C, hC, hc⟩ := List.any_eq_true.1 hl
  simp only [Bool.and_eq_true] at hc
  have h1 := hΓ C hC
  unfold Con.Holds at h1
  rw [ite_eq_left hc.1, val_eq_of_formEq hc.2, LF.val_add, LF.val_smul] at h1
  have ea := hI.val_coords (Sum.inl a) x v
  have eb := hI.val_coords (Sum.inl b) x v
  rw [show canon (Sum.inl a : Fin K ⊕ Fin m) = a from rfl] at ea
  rw [show canon (Sum.inl b : Fin K ⊕ Fin m) = b from rfl] at eb
  rw [ea, eb] at h1
  simp only [expo, Sum.elim_inl] at h1
  have hlx := Real.log_pos hx
  have hD := DEN_pos
  have h2 : DEN * (Real.log (v.1 b) / Real.log x) < DEN * (Real.log (v.1 a) / Real.log x) := by
    push_cast at h1
    linarith
  have h3 := (div_lt_div_iff_of_pos_right hlx).1 (lt_of_mul_lt_mul_left h2 hD.le)
  exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hv b) (by exact_mod_cast hv a)).1 h3

theorem strictAnti_of_succ : ∀ {n : ℕ} {f : Fin n → ℕ},
    (∀ i (hi : i + 1 < n), f ⟨i + 1, hi⟩ < f ⟨i, by omega⟩) → StrictAnti f
  | 0, _, _ => fun i => i.elim0
  | _ + 1, _, h => Fin.strictAnti_iff_succ_lt.2 fun i => h i (by omega)

/-- **The constraints order a chain** at the terms. -/
theorem strictAnti_chT {K m : ℕ} {A : Rows K m} {items : List LF} (hI : ItemsOK A items) {Γ : List Con}
    {c : List ℕ} (hc : chainOK Γ items c = true) (hcK : ∀ a ∈ c, a < K) {x : ℝ} (hx : 1 < x)
    {v : (Fin K → ℕ) × (Fin m → ℕ)} (hv : ∀ a, 0 < v.1 a) (hΓ : ∀ c ∈ Γ, c.Holds (coords A x v) (slack x v)) :
    StrictAnti (chT v.1 c) := by
  refine strictAnti_of_succ fun i hi => ?_
  have ha : c.getD i 0 < K := hcK _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hb : c.getD (i + 1) 0 < K := hcK _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
  simp only [chT, dite_eq_left ha, dite_eq_left hb]
  exact lt_of_linkOK hI (a := ⟨c.getD i 0, ha⟩) (b := ⟨c.getD (i + 1) 0, hb⟩) (linkOK_of_chainOK hc i hi) hx hv hΓ

/-- A prime is below its form's upper end on the box. -/
theorem lt_rpow_hiF {K m : ℕ} {A : Rows K m} {items : List LF} (hI : ItemsOK A items) {B : Box} {E : ℤ}
    (hfit : ∀ L ∈ items, L.c.length ≤ B.length) {x : ℝ} (hx : 1 < x) {v : (Fin K → ℕ) × (Fin m → ℕ)}
    (hv : ∀ a, 0 < v.1 a) (hB : InBox B (coords A x v)) (hH : |slack x v| ≤ E) (a : Fin K) :
    (v.1 a : ℝ) < x ^ ((hiF items B E a : ℝ) / DEN) := by
  have e := hI.val_coords (Sum.inl a) x v
  rw [show canon (Sum.inl a : Fin K ⊕ Fin m) = a from rfl] at e
  have h1 := (items.getD a LF.zero).le_maxB (length_getD_le hfit _) hB hH
  rw [e] at h1
  simp only [expo, Sum.elim_inl] at h1
  have hD := DEN_pos
  refine lt_rpow_of_div_lt hx (by exact_mod_cast hv a) ?_
  rw [lt_div_iff₀ hD]
  unfold hiF
  push_cast
  linarith

/-! ### The dropped node -/

/-- The members of a two-item node's chains: the primes of their forms' ranges, the items' sifting primes weighted by
`log x/(p log p)`. -/
noncomputable def twoMem (items : List LF) (B : Box) (E : ℤ) (sc sg : ℕ) : ℝ → ℕ → Finset ℕ × (ℕ → ℝ) :=
  genMem (fun a => loF items B E a) (fun a => hiF items B E a) (fun a => decide (a = sc ∨ a = sg))

/-- **A dropped node with two rough items, with the chain bound.** As `Sound.OK_of_drop2`, with the node's primes in
two chains `c` and `d` that the constraints order: the loss is `Ω_c Ω_g (hi_0 − lo_0)/DEN` times the product of any
limit superiors of the two chain sums below `x^{e_c/DEN}` and `x^{e_d/DEN}`, the `e` at least the chains' upper ends. -/
theorem Sound.OK_of_drop2C {K : ℕ} {s : Fin 2 → Fin K} {conds : List (Cond K 2)} {A : Rows K 2}
    {items : List LF} (hI : ItemsOK A items) {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound ⟨K, 2, s, conds⟩ A E Γ B) (hE : 0 < E) (hinv : Inv ⟨K, 2, s, conds⟩)
    (hfit : ∀ L ∈ items, L.c.length ≤ B.length) (hB0 : 0 < B.length) {g : Fin 2} (hsg : s g.rev ≠ s g)
    (hA0 : ∀ a, A 0 (Sum.inl a) = 0 ∨ A 0 (Sum.inl a) = 1) (hAg : A 0 (Sum.inr g) = 1)
    (hAc : A 0 (Sum.inr g.rev) = 0) (hlo : ∀ a : Fin K, 0 < loF items B E a)
    (hlohi : ∀ a : Fin K, loF items B E a ≤ hiF items B E a) (hNU : NU0 ≤ loF items B E (s g))
    (hlo0 : 0 < (B.getD 0 (0, 0)).1) (hlohi0 : (B.getD 0 (0, 0)).1 ≤ (B.getD 0 (0, 0)).2)
    {acts : List LF} (hacts : ∀ g ∈ acts, ∃ c ∈ Γ, c.L = g) (hfa : ∀ g ∈ acts, g.c.length ≤ B.length)
    (hn0 : 0 ≤ (numC (items.getD (K + g.rev) LF.zero)).minD B E acts) {Ωc Ωg : ℝ} (hΩc : 0 ≤ Ωc) (hΩg : 0 ≤ Ωg)
    (hωc : ∀ u : ℝ, ((numC (items.getD (K + g.rev) LF.zero)).minD B E acts : ℝ) / hiF items B E (s g.rev) ≤ u →
      u ≤ ((numC (items.getD (K + g.rev) LF.zero)).maxD B E acts : ℝ) / loF items B E (s g.rev) →
        SieveCert.omegaC u ≤ Ωc)
    (hωg : ∀ u : ℝ, (((B.getD 0 (0, 0)).1 : ℝ) - ∑ a ∈ univ.filter (fun a => A 0 (Sum.inl a) = 1),
        (hiF items B E a : ℝ)) / hiF items B E (s g) ≤ u →
      u ≤ (((B.getD 0 (0, 0)).2 : ℝ) - ∑ a ∈ univ.filter (fun a => A 0 (Sum.inl a) = 1), (loF items B E a : ℝ)) /
        loF items B E (s g) → SieveCert.omegaC u ≤ Ωg)
    {c d : List ℕ} (hnd : (c ++ d).Nodup) (hcov : ∀ a, a ∈ c ++ d ↔ a < K) (hc : chainOK Γ items c = true)
    (hd : chainOK Γ items d = true) {eC eD : ℤ} (heC : ∀ i < c.length, hiF items B E (c.getD i 0) ≤ eC)
    (heD : ∀ i < d.length, hiF items B E (d.getD i 0) ≤ eD) {Pc Pd : ℝ} (hPc0 : 0 ≤ Pc) (hPd0 : 0 ≤ Pd)
    (hPc : EvLe (fun x => chainSum (sfx (fun i => twoMem items B E (s g.rev) (s g) x (c.getD i 0)) c.length 0)
      (thr x eC)) Pc)
    (hPd : EvLe (fun x => chainSum (sfx (fun i => twoMem items B E (s g.rev) (s g) x (d.getD i 0)) d.length 0)
      (thr x eD)) Pd)
    {θ ρ : ℝ} (hρ : 0 < ρ) (hρ25 : 12 * ρ < 1 / 25) :
    OK θ ρ 1 (fun x y => ((⟨K, 2, s, conds⟩ : Node).count x y : ℝ))
      (Ωc * Ωg * ((((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN) * (Pc * Pd)) := by
  have hD := DEN_pos
  have hcK : ∀ a ∈ c, a < K := fun a ha => (hcov a).1 (List.mem_append_left _ ha)
  have hdK : ∀ a ∈ d, a < K := fun a ha => (hcov a).1 (List.mem_append_right _ ha)
  set M : ℝ → ℕ → Finset ℕ × (ℕ → ℝ) := twoMem items B E (s g.rev) (s g) with hM
  -- a chain's primes below its last breakpoint
  have hbelow : ∀ (ch : List ℕ) (e : ℤ), (∀ a ∈ ch, a < K) → (∀ i < ch.length, hiF items B E (ch.getD i 0) ≤ e) →
      ∀ x : ℝ, 1 < x → ∀ v : (Fin K → ℕ) × (Fin 2 → ℕ), (∀ a, 0 < v.1 a) → InBox B (coords A x v) →
        |slack x v| ≤ E → ∀ i, chT v.1 ch i < thr x e := by
    intro ch e hchK he x hx v hv hB hH i
    have ha : ch.getD i 0 < K := hchK _ (by rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem _)
    simp only [chT, dite_eq_left ha]
    refine Nat.lt_ceil.2 ((lt_rpow_hiF hI hfit hx hv hB hH ⟨_, ha⟩).trans_le
      (Real.rpow_le_rpow_of_exponent_le hx.le ?_))
    exact div_le_div_of_nonneg_right (by exact_mod_cast he i i.isLt) hD.le
  refine h.OK_of_drop2Q hI hE hinv hfit hB0 hA0 hAg hAc hlo hlohi hNU hlo0 hlohi0 hacts hfa hn0 hΩc hΩg hωc hωg
    (fun x p => (StrictAnti (chT p c) ∧ ∀ i, chT p c i < thr x eC) ∧ StrictAnti (chT p d) ∧
      ∀ i, chT p d i < thr x eD)
    (fun x hx v hv hH hB hΓ => ⟨⟨strictAnti_chT hI hc hcK hx hv hΓ, hbelow c eC hcK heC x hx v hv hB hH⟩,
      strictAnti_chT hI hd hdK hx hv hΓ, hbelow d eD hdK heD x hx v hv hB hH⟩)
    (mul_nonneg hPc0 hPd0) ?_ hρ hρ25
  -- the sum over the ordered box is at most the product of the chain sums
  have hmul := EvLe.mul hPc0 hPd0
    ((genMem_nonneg _ _ _).mono fun x hx => chainSum_nonneg _ (fun M' hM' p => by
      obtain ⟨i, -, -, rfl⟩ := mem_sfx hM'
      exact hx _ p) _)
    ((genMem_nonneg _ _ _).mono fun x hx => chainSum_nonneg _ (fun M' hM' p => by
      obtain ⟨i, -, -, rfl⟩ := mem_sfx hM'
      exact hx _ p) _) hPc hPd
  refine evLe_of_le hmul ?_
  filter_upwards [genMem_nonneg (fun a => loF items B E a) (fun a => hiF items B E a)
    (fun a => decide (a = (s g.rev : ℕ) ∨ a = s g))] with x hx
  refine le_trans (le_of_eq ?_) (sum_le_two_chains (M x) (fun a q => hx a q) c d hnd hcov (thr x eC) (thr x eD))
  refine sum_congr (by ext p; simp only [mem_filter]; exact Iff.rfl) fun p _ => ?_
  have e1 : ∀ j : Fin K, (M x j).2 (p j) = (1 / (p j : ℝ)) *
      (if j ∈ ({s g.rev, s g} : Finset (Fin K)) then Real.log x / Real.log (p j) else 1) := fun j => by
    simp only [hM, twoMem, genMem, decide_eq_true_eq, Fin.val_inj, Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> ring
  rw [prod_congr rfl fun j _ => e1 j, prod_mul_distrib, prod_ite_mem, univ_inter, prod_pair hsg, prod_div_distrib,
    prod_const_one]
  ring

end ShortSieveCert
