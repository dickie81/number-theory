import ShortSieveCertTwo

/-!
# The certificate's dropped boxes with two rough items

A node with two rough items and positive sign may be dropped (`ShortSieveDrop.count_le_drop2`). The item `c` is the
cofactor, bounded by `ω*` and the rough numbers of the comparison interval. The item `g` is summed over its range:
its product with the primes `J` is the coordinate `0`, in the box's range.

* `Sound.OK_of_drop2Q`: on a sound node with two rough items whose coordinate `0` is the product of the item `g` and the
  primes with coefficient `1`, the node is `OK` for `σ = 1` with loss `Ω_c Ω_g (hi_0 − lo_0)/DEN · P`, for any limit
  superior `P` of the sum over the primes of the box that satisfy a condition the node's primes satisfy, the primes'
  ranges from their forms.
* `Sound.OK_of_drop2`: the same with `P = ∏_j (DEN/lo_j − DEN/hi_j or trB(lo_j, hi_j))`.
-/

open Finset Real Filter

namespace ShortSieveCert

open ShortSieveNode ShortSieveExpand ShortSieveBuch ShortSieveTree

open Classical

/-- The coordinate `0` as the item `g` times the primes with coefficient `1`. -/
theorem cX_zero_eq {K : ℕ} {A : Rows K 2} {g : Fin 2} (hA0 : ∀ a, A 0 (Sum.inl a) = 0 ∨ A 0 (Sum.inl a) = 1)
    (hAg : A 0 (Sum.inr g) = 1) (hAc : A 0 (Sum.inr g.rev) = 0) (α : Fin K ⊕ Fin 2 → ℝ) :
    cX A α 0 = DEN * (∑ a ∈ univ.filter (fun a => A 0 (Sum.inl a) = 1), α (Sum.inl a) + α (Sum.inr g)) := by
  unfold cX
  congr 1
  rw [Fintype.sum_sum_type, sum_filter]
  congr 1
  · refine sum_congr rfl fun a _ => ?_
    rcases hA0 a with h | h <;> simp [h]
  · rw [Fin.sum_univ_two]
    have hi : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hi with rfl | rfl
    · rw [show (0 : Fin 2).rev = 1 from rfl] at hAc
      simp [hAg, hAc]
    · rw [show (1 : Fin 2).rev = 0 from rfl] at hAc
      simp [hAg, hAc]

/-- The cofactor's numerator form `F + H`: `DEN log(x/(∏p · γ))/log x` at a pair's coordinates. -/
def numC (F : LF) : LF := ⟨F.c0, F.c, F.ce + 1⟩

theorem val_numC (F : LF) (X : ℕ → ℝ) (H : ℝ) : (numC F).val X H = F.val X H + H := by
  unfold numC LF.val
  push_cast
  ring

/-- A prime's lower end on the box, from its form. -/
def loF (items : List LF) (B : Box) (E : ℤ) (a : ℕ) : ℤ := (items.getD a LF.zero).min B E

/-- A prime's upper end on the box, from its form (strict, hence the `1`). -/
def hiF (items : List LF) (B : Box) (E : ℤ) (a : ℕ) : ℤ := (items.getD a LF.zero).maxB B E + 1

/-- The sum over a two-element set of indices. -/
theorem sum_fin_two_rev (f : Fin 2 → ℝ) (g : Fin 2) : ∑ i, f i = f g.rev + f g := by
  rw [Fin.sum_univ_two]
  have hi : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  rcases hi with rfl | rfl
  · rw [show (0 : Fin 2).rev = 1 from rfl]; ring
  · rw [show (1 : Fin 2).rev = 0 from rfl]

theorem rev_ne_self (g : Fin 2) : g.rev ≠ g := by fin_cases g <;> decide

/-- **A dropped node with two rough items, its primes in a set.** On a sound node with two rough items whose
coordinate `0` is the product of the item `g` and the primes with coefficient `1`, with `Ω_c`, `Ω_g` bounds for `ω*` on
the box's ranges of the cofactor's argument `log(x/(∏p · γ_g))/log p_{s(c)}` (`c` the other item) and of
`log γ/log p_{s(g)}`, the node is `OK` for `σ = 1` with loss `Ω_c Ω_g (hi_0 − lo_0)/DEN · P`, if the node's primes
satisfy `Q` (from the box and the constraints) and `P` bounds the limit superior of the sum over the box's primes that
satisfy `Q`. -/
theorem Sound.OK_of_drop2Q {K : ℕ} {s : Fin 2 → Fin K} {conds : List (Cond K 2)} {A : Rows K 2}
    {items : List LF} (hI : ItemsOK A items) {E : ℤ} {Γ : List Con} {B : Box}
    (h : Sound ⟨K, 2, s, conds⟩ A E Γ B) (hE : 0 < E) (hinv : Inv ⟨K, 2, s, conds⟩)
    (hfit : ∀ L ∈ items, L.c.length ≤ B.length) (hB0 : 0 < B.length) {g : Fin 2}
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
    (Q : ℝ → (Fin K → ℕ) → Prop)
    (hQ : ∀ x : ℝ, 1 < x → ∀ v : (Fin K → ℕ) × (Fin 2 → ℕ), (∀ a, 0 < v.1 a) → |slack x v| ≤ E →
      InBox B (coords A x v) → (∀ c ∈ Γ, c.Holds (coords A x v) (slack x v)) → Q x v.1)
    {P : ℝ} (hP0 : 0 ≤ P)
    (hF : SieveRough.EvLe (fun x => ∑ p ∈ (Fintype.piFinset fun j : Fin K => SieveRough.primesIn
        (x ^ ((loF items B E j : ℝ) / DEN)) (x ^ ((hiF items B E j : ℝ) / DEN))).filter (Q x),
      Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s g.rev)) * Real.log (p (s g)))) P)
    {θ ρ : ℝ} (hρ : 0 < ρ) (hρ20 : 12 * ρ < 1 / 20) :
    OK θ ρ 1 (fun x y => ((⟨K, 2, s, conds⟩ : Node).count x y : ℝ))
      (Ωc * Ωg * ((((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN) * P) := by
  have hD := DEN_pos
  set J := univ.filter (fun a : Fin K => A 0 (Sum.inl a) = 1) with hJ
  set lo : Fin K → ℝ := fun j => (loF items B E j : ℝ) / DEN with hlo_def
  set hi : Fin K → ℝ := fun j => (hiF items B E j : ℝ) / DEN with hhi_def
  have hloR : ∀ j : Fin K, (0 : ℝ) < loF items B E j := fun j => by exact_mod_cast hlo j
  have hlohiR : ∀ j : Fin K, (loF items B E j : ℝ) ≤ hiF items B E j := fun j => by exact_mod_cast hlohi j
  have hlo' : ∀ j, 0 < lo j := fun j => div_pos (hloR j) hD
  have hlohi' : ∀ j, lo j ≤ hi j := fun j => div_le_div_of_nonneg_right (hlohiR j) hD.le
  set L0 : ℝ := ((B.getD 0 (0, 0)).1 : ℝ) with hL0
  set H0 : ℝ := ((B.getD 0 (0, 0)).2 : ℝ) with hH0
  have hL0pos : 0 < L0 := by rw [hL0]; exact_mod_cast hlo0
  have hL0H0 : L0 ≤ H0 := by rw [hL0, hH0]; exact_mod_cast hlohi0
  -- the primes' exponents at a pair in the box
  have hrange : ∀ (x : ℝ) (v : (Fin K → ℕ) × (Fin 2 → ℕ)), InBox B (coords A x v) → |slack x v| ≤ E →
      ∀ a : Fin K, (loF items B E a : ℝ) ≤ DEN * expo x v (Sum.inl a) ∧
        DEN * expo x v (Sum.inl a) < hiF items B E a := by
    intro x v hB hH a
    have e := hI.val_coords (Sum.inl a) x v
    rw [show canon (Sum.inl a : Fin K ⊕ Fin 2) = a from rfl] at e
    rw [← e]
    refine ⟨(items.getD a LF.zero).min_le (length_getD_le hfit _) hB hH, ?_⟩
    have := (items.getD a LF.zero).le_maxB (length_getD_le hfit _) hB hH
    unfold hiF
    push_cast
    linarith
  -- the node's terms in the comparison interval
  have hterm : ∀ᶠ x : ℝ in atTop, ∀ v ∈ pairs K 2 ⌊x⌋₊, (∀ i, SieveTree.rough (v.1 (s i)) (v.2 i)) →
      (⟨K, 2, s, conds⟩ : Node).InI x (x ^ (1 - ρ)) v.1 v.2 →
        v.1 ∈ (Fintype.piFinset fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j)).filter (Q x) ∧
          x ^ (1 / 20 : ℝ) ≤ v.1 (s g.rev) ∧ (v.1 (s g.rev) : ℝ) ≤ v.2 g.rev ∧ (v.1 (s g) : ℝ) ≤ v.2 g ∧
          x ^ (L0 / DEN) ≤ (∏ j ∈ J, (v.1 j : ℝ)) * v.2 g ∧ (∏ j ∈ J, (v.1 j : ℝ)) * v.2 g ≤ x ^ (H0 / DEN) ∧
          SieveCert.omegaC (Real.log (x / ((∏ j, (v.1 j : ℝ)) * v.2 g)) / Real.log (v.1 (s g.rev))) ≤ Ωc := by
    filter_upwards [abs_slack_le hE K 2, eventually_gt_atTop 1,
      (tendsto_rpow_atTop hρ).eventually_ge_atTop 2] with x hsl hx1 hxr v hv _ hI'
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx1
    obtain ⟨hp, hρ'⟩ := mem_pairs.1 hv
    have hv1 : ∀ a, 0 < v.1 a := fun a => (hp a).2.pos
    have hv2 : ∀ i, 0 < v.2 i := fun i => (hρ' i).1
    have hyx : x ^ (1 - ρ) ≤ x / 2 := by
      have e : x ^ (1 - ρ) * x ^ ρ = x := by rw [← Real.rpow_add hx0]; simp
      have : x ^ (1 - ρ) * 2 ≤ x := by
        calc x ^ (1 - ρ) * 2 ≤ x ^ (1 - ρ) * x ^ ρ := mul_le_mul_of_nonneg_left hxr (Real.rpow_nonneg hx0.le _)
          _ = x := e
      linarith
    obtain ⟨hcI, h1, h2⟩ := hI'
    have hH := hsl v hv1 hv2 (by linarith) (by linarith)
    obtain ⟨hB, hΓ⟩ := h x hx1 v hv1 hv2 hcI hH
    obtain ⟨hall, hge⟩ := hinv x hx1 v hv1 hv2 hcI
    have hpj : ∀ j, (0 : ℝ) < v.1 j := fun j => by exact_mod_cast hv1 j
    have hqi : ∀ i, (0 : ℝ) < v.2 i := fun i => by exact_mod_cast hv2 i
    have hr := hrange x v hB hH
    have hprodpos : (0 : ℝ) < (∏ j ∈ J, (v.1 j : ℝ)) * v.2 g := mul_pos (prod_pos fun j _ => hpj j) (hqi g)
    -- the product of `g` and the primes `J` is the coordinate `0`
    have hprod : coords A x v 0 = DEN * (Real.log ((∏ j ∈ J, (v.1 j : ℝ)) * v.2 g) / Real.log x) := by
      rw [coords_eq, cX_zero_eq hA0 hAg hAc, Real.log_mul (prod_pos fun j _ => hpj j).ne' (hqi g).ne',
        Real.log_prod fun j _ => (hpj j).ne']
      simp only [expo, Sum.elim_inl, Sum.elim_inr]
      rw [add_div, sum_div]
    have hb0 := inBox_getD B _ 0 hB hB0
    rw [hprod] at hb0
    refine ⟨mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => SieveRough.mem_primesIn.2 ⟨(hp j).2, ?_, ?_⟩,
      hQ x hx1 v hv1 hH hB hΓ⟩, hall _,
      by exact_mod_cast hge g.rev, by exact_mod_cast hge g, ?_, ?_, ?_⟩
    · refine rpow_le_of_le_div hx1 (hpj j) ?_
      rw [hlo_def, div_le_iff₀ hD]
      have := (hr j).1
      simp only [expo, Sum.elim_inl] at this
      linarith
    · refine lt_rpow_of_div_lt hx1 (hpj j) ?_
      rw [hhi_def, lt_div_iff₀ hD]
      have := (hr j).2
      simp only [expo, Sum.elim_inl] at this
      linarith
    · refine rpow_le_of_le_div hx1 hprodpos ?_
      rw [div_le_iff₀ hD]
      linarith [hb0.1]
    · refine (lt_rpow_of_div_lt hx1 hprodpos ?_).le
      rw [lt_div_iff₀ hD]
      linarith [hb0.2]
    · -- the cofactor's argument `u = (DEN α_c + H)/(DEN α_{s(c)})`
      have hacts' : ∀ g' ∈ acts, g'.val (coords A x v) (slack x v) ≤ 0 := fun g' hg' => by
        obtain ⟨c, hc', rfl⟩ := hacts g' hg'
        exact Con.val_le (hΓ c hc')
      set Nc := numC (items.getD (K + g.rev) LF.zero) with hNc
      have hfitN : Nc.c.length ≤ B.length := by simpa [hNc, numC] using length_getD_le hfit (K + g.rev)
      have hmin := Nc.minD_le acts (inBoxC_of_inBox hB) hH hacts' hfitN hfa
      have hmax := Nc.le_maxD acts (inBoxC_of_inBox hB) hH hacts' hfitN hfa
      set Nv := Nc.val (coords A x v) (slack x v) with hNv
      have eN : Nv = DEN * (Real.log (x / ((∏ j, (v.1 j : ℝ)) * v.2 g)) / Real.log x) := by
        have e1 := hI.val_coords (Sum.inr g.rev) x v
        rw [show canon (Sum.inr g.rev : Fin K ⊕ Fin 2) = K + g.rev from rfl] at e1
        rw [hNv, hNc, val_numC, e1]
        unfold slack
        rw [Fintype.sum_sum_type, sum_fin_two_rev _ g,
          Real.log_div hx0.ne' (mul_pos (prod_pos fun j _ => hpj j) (hqi g)).ne',
          Real.log_mul (prod_pos fun j _ => hpj j).ne' (hqi g).ne', Real.log_prod fun j _ => (hpj j).ne']
        simp only [expo, Sum.elim_inl, Sum.elim_inr]
        rw [← sum_div]
        field_simp
        ring
      set D := DEN * expo x v (Sum.inl (s g.rev)) with hD_def
      have hDlo := (hr (s g.rev)).1
      have hDhi := (hr (s g.rev)).2
      have hDpos : 0 < D := lt_of_lt_of_le (hloR _) hDlo
      have hu : Real.log (x / ((∏ j, (v.1 j : ℝ)) * v.2 g)) / Real.log (v.1 (s g.rev)) = Nv / D := by
        rw [eN, hD_def]
        simp only [expo, Sum.elim_inl]
        have hlp : 0 < Real.log (v.1 (s g.rev)) := by
          have := hDpos
          rw [hD_def] at this
          simp only [expo, Sum.elim_inl] at this
          exact (div_pos_iff_of_pos_right hlx).1 (pos_of_mul_pos_right this hD.le)
        field_simp
      rw [hu]
      have hn0' : (0 : ℝ) ≤ Nc.minD B E acts := by exact_mod_cast hn0
      refine hωc _ ?_ ?_
      · exact div_le_div₀ (hn0'.trans hmin) hmin hDpos hDhi.le
      · exact div_le_div₀ ((hn0'.trans hmin).trans hmax) hmax (hloR _) hDlo
  -- the boxes of primes: the range of `log γ/log p_{s(g)}`
  have hPB : ∀ᶠ x : ℝ in atTop, ∀ p ∈ (Fintype.piFinset fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j)).filter
      (Q x),
      x ^ (1 / 20 : ℝ) ≤ p (s g) ∧ (∀ j, 1 ≤ p j) ∧ ∀ X : ℝ, x ^ (L0 / DEN) / ∏ j ∈ J, (p j : ℝ) ≤ X →
        X ≤ x ^ (H0 / DEN) / ∏ j ∈ J, (p j : ℝ) → SieveCert.omegaC (Real.log X / Real.log (p (s g))) ≤ Ωg := by
    filter_upwards [eventually_gt_atTop 1] with x hx1 p hp
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have hpm := fun j => SieveRough.mem_primesIn.1 (Fintype.mem_piFinset.1 (mem_filter.1 hp).1 j)
    have hpj : ∀ j, (0 : ℝ) < p j := fun j => by exact_mod_cast (hpm j).1.pos
    have hlogp : ∀ j, lo j * Real.log x ≤ Real.log (p j) ∧ Real.log (p j) < hi j * Real.log x := fun j => by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) (hpm j).2.1
      have h2 := Real.log_lt_log (hpj j) (hpm j).2.2
      rw [Real.log_rpow hx0] at h1 h2
      exact ⟨h1, h2⟩
    have h20 : (1 / 20 : ℝ) ≤ lo (s g) := by
      have h := (show ((NU0 : ℤ) : ℝ) ≤ loF items B E (s g) by exact_mod_cast hNU)
      rw [NU0_eq] at h
      rw [hlo_def, le_div_iff₀ hD]
      linarith
    refine ⟨(Real.rpow_le_rpow_of_exponent_le hx1.le h20).trans (hpm (s g)).2.1,
      fun j => (hpm j).1.one_lt.le, fun X hX1 hX2 => ?_⟩
    by_cases hu1 : Real.log X / Real.log (p (s g)) < 1
    · unfold SieveCert.omegaC
      rw [ite_eq_left hu1]
      exact hΩg
    push Not at hu1
    -- `log X ≥ log p_{s(g)} > 0`
    have hlg : 0 < Real.log (p (s g)) := lt_of_lt_of_le (mul_pos (hlo' _) hlx) (hlogp (s g)).1
    have hlX : Real.log (p (s g)) ≤ Real.log X := by rwa [le_div_iff₀ hlg, one_mul] at hu1
    have hPJ : (0 : ℝ) < ∏ j ∈ J, (p j : ℝ) := prod_pos fun j _ => hpj j
    have hXpos : 0 < X := lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hx0 _) hPJ) hX1
    have hlogPJ : Real.log (∏ j ∈ J, (p j : ℝ)) = ∑ j ∈ J, Real.log (p j) := Real.log_prod fun j _ => (hpj j).ne'
    -- `log X` within `[L0/DEN log x − Σ_J log p_j, H0/DEN log x − Σ_J log p_j]`
    have hX1' : L0 / DEN * Real.log x - ∑ j ∈ J, Real.log (p j) ≤ Real.log X := by
      have := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hx0 _) hPJ) hX1
      rwa [Real.log_div (Real.rpow_pos_of_pos hx0 _).ne' hPJ.ne', Real.log_rpow hx0, hlogPJ] at this
    have hX2' : Real.log X ≤ H0 / DEN * Real.log x - ∑ j ∈ J, Real.log (p j) := by
      have := Real.log_le_log hXpos hX2
      rwa [Real.log_div (Real.rpow_pos_of_pos hx0 _).ne' hPJ.ne', Real.log_rpow hx0, hlogPJ] at this
    have hJlo : ∑ j ∈ J, lo j * Real.log x ≤ ∑ j ∈ J, Real.log (p j) := sum_le_sum fun j _ => (hlogp j).1
    have hJhi : ∑ j ∈ J, Real.log (p j) ≤ ∑ j ∈ J, hi j * Real.log x := sum_le_sum fun j _ => (hlogp j).2.le
    refine hωg _ ?_ ?_
    · -- the lower end
      set N := L0 - ∑ a ∈ J, (hiF items B E a : ℝ) with hN
      have hNX : N / DEN * Real.log x ≤ Real.log X := by
        have e : N / DEN * Real.log x = L0 / DEN * Real.log x - ∑ j ∈ J, hi j * Real.log x := by
          rw [hN]
          simp only [hhi_def, sub_div, sum_div, sub_mul, sum_mul]
        rw [e]
        linarith
      rcases le_or_gt N 0 with hN0 | hN0
      · have : N / hiF items B E (s g) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hN0 (by linarith [hloR (s g), hlohiR (s g)])
        exact this.trans (div_nonneg (by linarith) hlg.le)
      · have hHg : (0 : ℝ) < hiF items B E (s g) := lt_of_lt_of_le (hloR _) (hlohiR _)
        have hlg' : Real.log (p (s g)) < hiF items B E (s g) / DEN * Real.log x := (hlogp (s g)).2
        rw [div_le_div_iff₀ hHg hlg]
        have h1 : N * Real.log (p (s g)) ≤ N * (hiF items B E (s g) / DEN * Real.log x) :=
          mul_le_mul_of_nonneg_left hlg'.le hN0.le
        have h2 : N / DEN * Real.log x * hiF items B E (s g) ≤ Real.log X * hiF items B E (s g) :=
          mul_le_mul_of_nonneg_right hNX hHg.le
        have e : N * (hiF items B E (s g) / DEN * Real.log x) = N / DEN * Real.log x * hiF items B E (s g) := by
          ring
        linarith
    · -- the upper end
      set N := H0 - ∑ a ∈ J, (loF items B E a : ℝ) with hN
      have hNX : Real.log X ≤ N / DEN * Real.log x := by
        have e : N / DEN * Real.log x = H0 / DEN * Real.log x - ∑ j ∈ J, lo j * Real.log x := by
          rw [hN]
          simp only [hlo_def, sub_div, sum_div, sub_mul, sum_mul]
        rw [e]
        linarith
      have hN0 : 0 < N := by
        have : 0 < N / DEN * Real.log x := lt_of_lt_of_le (lt_of_lt_of_le hlg hlX) hNX
        exact (div_pos_iff_of_pos_right hD).1 (pos_of_mul_pos_left this hlx.le)
      have hLg := hloR (s g)
      have hlg' : loF items B E (s g) / DEN * Real.log x ≤ Real.log (p (s g)) := (hlogp (s g)).1
      rw [div_le_div_iff₀ hlg hLg]
      have h1 : Real.log X * loF items B E (s g) ≤ N / DEN * Real.log x * loF items B E (s g) :=
        mul_le_mul_of_nonneg_right hNX hLg.le
      have h2 : N * (loF items B E (s g) / DEN * Real.log x) ≤ N * Real.log (p (s g)) :=
        mul_le_mul_of_nonneg_left hlg' hN0.le
      have e : N * (loF items B E (s g) / DEN * Real.log x) = N / DEN * Real.log x * loF items B E (s g) := by
        ring
      linarith
  have hdrop : OK θ ρ 1 (fun x y => ((⟨K, 2, s, conds⟩ : Node).count x y : ℝ))
      (Ωc * Ωg * (H0 / DEN - L0 / DEN) * P) :=
    ShortSieveTree.OK_of_drop (fun x y => Nat.cast_nonneg _) fun δ hδ =>
      ShortSieveDrop.count_le_drop2 s conds (rev_ne_self g) J (lo := 1 / 20) (by norm_num) hρ hρ20
        (div_pos hL0pos hD) (div_le_div_of_nonneg_right hL0H0 hD.le) hΩc hΩg hP0 _ hterm hPB hF hδ
  refine OK_mono (le_of_eq ?_) hdrop
  ring

/-- **A dropped node with two rough items.** On a sound node with two rough items whose coordinate `0` is the product
of the item `g` and the primes with coefficient `1`, the other item `c` (the cofactor) and `g` sifted by distinct
primes, and with `Ω_c`, `Ω_g` bounds for `ω*` on the box's ranges of the cofactor's argument
`log(x/(∏p · γ_g))/log p_{s(c)}` and of `log γ/log p_{s(g)}`, the node is `OK` for `σ = 1` with loss
`Ω_c Ω_g (hi_0 − lo_0)/DEN · ∏_j (DEN/lo_j − DEN/hi_j or trB(lo_j, hi_j))`. -/
theorem Sound.OK_of_drop2 {K : ℕ} {s : Fin 2 → Fin K} {conds : List (Cond K 2)} {A : Rows K 2}
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
    {θ ρ : ℝ} (hρ : 0 < ρ) (hρ20 : 12 * ρ < 1 / 20) :
    OK θ ρ 1 (fun x y => ((⟨K, 2, s, conds⟩ : Node).count x y : ℝ))
      (Ωc * Ωg * ((((B.getD 0 (0, 0)).2 : ℝ) - (B.getD 0 (0, 0)).1) / DEN) *
        ∏ j : Fin K, if j ∈ ({s g.rev, s g} : Finset (Fin K)) then (DEN : ℝ) / loF items B E j -
          DEN / hiF items B E j else trB (loF items B E j) (hiF items B E j)) := by
  have hD := DEN_pos
  set J := univ.filter (fun a : Fin K => A 0 (Sum.inl a) = 1) with hJ
  set lo : Fin K → ℝ := fun j => (loF items B E j : ℝ) / DEN with hlo_def
  set hi : Fin K → ℝ := fun j => (hiF items B E j : ℝ) / DEN with hhi_def
  have hloR : ∀ j : Fin K, (0 : ℝ) < loF items B E j := fun j => by exact_mod_cast hlo j
  have hlohiR : ∀ j : Fin K, (loF items B E j : ℝ) ≤ hiF items B E j := fun j => by exact_mod_cast hlohi j
  have hlo' : ∀ j, 0 < lo j := fun j => div_pos (hloR j) hD
  have hlohi' : ∀ j, lo j ≤ hi j := fun j => div_le_div_of_nonneg_right (hlohiR j) hD.le
  set L0 : ℝ := ((B.getD 0 (0, 0)).1 : ℝ) with hL0
  set H0 : ℝ := ((B.getD 0 (0, 0)).2 : ℝ) with hH0
  have hL0pos : 0 < L0 := by rw [hL0]; exact_mod_cast hlo0
  have hL0H0 : L0 ≤ H0 := by rw [hL0, hH0]; exact_mod_cast hlohi0
  set P : ℝ := ∏ j, if j ∈ ({s g.rev, s g} : Finset (Fin K)) then 1 / lo j - 1 / hi j
    else Real.log (hi j) - Real.log (lo j) with hP_def
  have hP0 : 0 ≤ P := prod_nonneg fun j _ => by
    split_ifs
    · have := one_div_le_one_div_of_le (hlo' j) (hlohi' j); linarith
    · have := Real.log_le_log (hlo' j) (hlohi' j); linarith
  -- Mertens' sums over the box
  have hF : SieveRough.EvLe (fun x => ∑ p ∈ Fintype.piFinset (fun j => SieveRough.primesIn (x ^ lo j) (x ^ hi j)),
      Real.log x ^ 2 / ((∏ j, (p j : ℝ)) * Real.log (p (s g.rev)) * Real.log (p (s g)))) P := by
    intro δ hδ
    filter_upwards [ShortSieveDrop.evLe_box lo hi hlo' hlohi' {s g.rev, s g} δ hδ] with x hx
    refine le_trans (le_of_eq (sum_congr rfl fun p _ => ?_)) hx
    have e1 : ∀ j, (if j ∈ ({s g.rev, s g} : Finset (Fin K)) then Real.log x / ((p j : ℝ) * Real.log (p j))
        else 1 / (p j : ℝ)) = (1 / (p j : ℝ)) *
          (if j ∈ ({s g.rev, s g} : Finset (Fin K)) then Real.log x / Real.log (p j) else 1) := fun j => by
      split_ifs <;> ring
    rw [prod_congr rfl fun j _ => e1 j, prod_mul_distrib, prod_ite_mem, univ_inter, prod_pair hsg,
      prod_div_distrib, prod_const_one]
    ring
  have hdrop := h.OK_of_drop2Q hI hE hinv hfit hB0 hA0 hAg hAc hlo hlohi hNU hlo0 hlohi0 hacts hfa hn0 hΩc hΩg hωc hωg
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) hP0
    (by convert hF using 3; ext p; simp only [mem_filter, and_true]; exact Iff.rfl) (θ := θ) hρ hρ20
  refine OK_mono ?_ hdrop
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_)
    (mul_nonneg (mul_nonneg hΩc hΩg) (div_nonneg (by linarith) hD.le))
  · split_ifs
    · have := one_div_le_one_div_of_le (hlo' j) (hlohi' j); linarith
    · have := Real.log_le_log (hlo' j) (hlohi' j); linarith
  · by_cases hj : j ∈ ({s g.rev, s g} : Finset (Fin K))
    · simp only [hj, ite_true, hlo_def, hhi_def, one_div_div]
      exact le_rfl
    · simp only [hj, ite_false, hlo_def, hhi_def]
      rw [Real.log_div (by linarith [hloR j, hlohiR j]) hD.ne', Real.log_div (hloR j).ne' hD.ne']
      have := log_le_trB (hloR j) (hlohiR j)
      linarith

end ShortSieveCert

#print axioms ShortSieveCert.Sound.OK_of_drop2
