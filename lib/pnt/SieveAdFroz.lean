/-
# A tree of Buchstab steps over a frozen part

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. A reversed term is a sum over numbers `R` (the product `r'` of the term's other primes and its
cofactor) of the `n = R·N` whose quotient `N` is sifted: Buchstab's identity brings out a chain `c₁ > ⋯ > c_t` of
primes of `N`, and the term of the chain's box is the sum over `R` and the chain of the `n` with `R·c₁⋯c_t | n`
and `n/R` with no prime factor below `c_t`. The primes of `R` play no part in the steps: a prime of the chain may
lie above some of them. `SieveAdRev.lean` has the case where the chain lies below every prime of `R`, which is one
family of tuples; here `R` runs over any finite family, the **frozen part**.

* `famI_cutN`, `famI_buchN`: the cut of a cell and Buchstab's identity on a box (`SieveAd.famI_cut`,
  `famI_buch`), for the sums over any range `(N₁, N₂]`.
* `sum_Ioc_mul`: a sum over `N ∈ (N₁/R, N₂/R]` of a function of `R·N` is the sum over the multiples of `R` in
  `(N₁, N₂]`.
* `famIR`, `famJR`: the term of a family of chains, and its terms at a level, on the multiples `n = R·N` of `R`:
  the family's terms for the weight `N ↦ g(R·N)` on `(N₁/R, N₂/R]`. `famIR_eq`, `famJR_eq`: as sums over
  `n ∈ (N₁, N₂]`, of `g(n)` for `R·∏c | n` and `n/R` with no prime factor below the chain's last prime, or below
  the level.
* `WF`: the sum of `1/R` over a frozen part, the weight of the costs. `dIF`, `dJF`: the term of a chain's box over
  a frozen part, and its terms at a floor, in `𝒜` minus the comparison set. `dIF_cut`, `dIF_buch`: the cut of a
  cell of the chain and Buchstab's identity on the chain.
* `BdF S R par C bx`: the term, with its sign, is at least `−(C·WF + o(1))x/(φ(q) log x)`; `EvIF`, `EvJF`: the
  term, or the terms at a floor, are evaluated. `bdF_eval`, `bdF_mono`, `bdF_split`, `bdF_buch`: the nodes of a
  tree, as `SieveAd.bdP_eval` and the lemmas after it.

The file imports `SieveAdFilt.lean`.
-/
import SieveAdFilt

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

variable [Route]

/-! ### The steps on any range -/

/-- **A cut**, on any range: for `lo_i ≤ c ≤ hi_i`, the term of a box is the sum of the terms of the boxes with
the cell `i` cut at `c`. -/
theorem famI_cutN (g : ℕ → ℝ) (N₁ N₂ : ℕ) {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell)
    (i : Fin (k' + 1)) {c : ℕ} (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) :
    famI g N₁ N₂ (famB q bx) =
      famI g N₁ N₂ (famB q (Function.update bx i ((bx i).1, c))) +
        famI g N₁ N₂ (famB q (Function.update bx i (c, (bx i).2))) := by
  unfold famI
  rw [famB_cut_lo hx bx i h2, famB_cut_hi hx bx i h1, Finset.sum_filter_add_sum_filter_not]

/-- **Buchstab's identity on a box**, on any range, with the floor `z = ⌈x^{f/DEN}⌉` for `f ≤ lo_last`. -/
theorem famI_buchN (g : ℕ → ℝ) (N₁ N₂ : ℕ) {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) :
    famI g N₁ N₂ (famB q bx) =
      famJ g N₁ N₂ ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (famB q bx) -
        famI g N₁ N₂ (famB q (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))) := by
  have hpt : ∀ rt ∈ famB q bx, ∀ n ∈ Ioc N₁ N₂,
      g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
        g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ n then 1 else 0) -
          ∑ p ∈ SieveTree.primesIco ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (rt (Fin.last k')),
            g n * (if (∏ i, (Fin.snoc rt p : Fin (k' + 2) → ℕ) i) ∣ n ∧
              SieveTree.rough ((Fin.snoc rt p : Fin (k' + 2) → ℕ) (Fin.last _)) n then 1 else 0) := by
    intro rt hrt n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hn).1; omega
    exact buch_pt_box hrt (ceil_le_last hx hrt hf) g hn0
  unfold famI famJ
  rw [Finset.sum_congr rfl fun rt hrt => Finset.sum_congr rfl (hpt rt hrt)]
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [← famB_snoc_sum q bx f]
  refine Finset.sum_congr rfl fun rt _ => ?_
  exact Finset.sum_comm

/-! ### Terms on the multiples of a number -/

omit [Route] in
/-- A sum over `N ∈ (N₁/R, N₂/R]` of a function of `R·N` is the sum over the multiples of `R` in `(N₁, N₂]`. -/
theorem sum_Ioc_mul {R : ℕ} (hR : 0 < R) (N₁ N₂ : ℕ) (G : ℕ → ℝ) :
    ∑ N ∈ Ioc (N₁ / R) (N₂ / R), G (R * N) = ∑ n ∈ Ioc N₁ N₂, if R ∣ n then G n else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun N => R * N) (fun n => n / R) ?_ ?_ ?_ ?_ ?_
  · intro N hN
    rw [Finset.mem_Ioc] at hN
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right R N⟩
    · have := (Nat.div_lt_iff_lt_mul hR).1 hN.1
      rwa [mul_comm] at this
    · have := (Nat.le_div_iff_mul_le hR).1 hN.2
      rwa [mul_comm] at this
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨h1, h2⟩, c, rfl⟩ := hn
    rw [Finset.mem_Ioc, Nat.mul_div_cancel_left c hR]
    exact ⟨(Nat.div_lt_iff_lt_mul hR).2 (by rwa [mul_comm] at h1),
      (Nat.le_div_iff_mul_le hR).2 (by rwa [mul_comm] at h2)⟩
  · intro N _
    exact Nat.mul_div_cancel_left N hR
  · intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro N _
    rfl

/-- The term of a family of chains on the multiples `n = R·N` of `R`: the family's term for the weight
`N ↦ g(R·N)` on `(N₁/R, N₂/R]`. -/
noncomputable def famIR (g : ℕ → ℝ) (N₁ N₂ R : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) : ℝ :=
  famI (fun N => g (R * N)) (N₁ / R) (N₂ / R) F

/-- The terms at the level `z` of a family of chains on the multiples `n = R·N` of `R`. -/
noncomputable def famJR (g : ℕ → ℝ) (N₁ N₂ z R : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) : ℝ :=
  famJ (fun N => g (R * N)) (N₁ / R) (N₂ / R) z F

omit [Route] in
/-- For `R ∣ n`: `R·W ∣ n` exactly when `W ∣ n/R`. -/
theorem mul_dvd_iff_dvd_div {R W n : ℕ} (hR : 0 < R) (h : R ∣ n) : R * W ∣ n ↔ W ∣ n / R := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left c hR]
  exact Nat.mul_dvd_mul_iff_left hR

omit [Route] in
/-- **The term on the multiples of `R`, as a sum over `n`**: the `n ∈ (N₁, N₂]` with `R·∏c ∣ n` and `n/R` free
of primes below the chain's last. -/
theorem famIR_eq (g : ℕ → ℝ) (N₁ N₂ : ℕ) {R : ℕ} (hR : 0 < R) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) :
    famIR g N₁ N₂ R F = ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂,
      g n * (if R * ∏ i, rt i ∣ n ∧ SieveTree.rough (rt (Fin.last k')) (n / R) then 1 else 0) := by
  unfold famIR famI
  refine Finset.sum_congr rfl fun rt _ => ?_
  have e : ∀ N ∈ Ioc (N₁ / R) (N₂ / R),
      g (R * N) * (if (∏ i, rt i) ∣ N ∧ SieveTree.rough (rt (Fin.last k')) N then (1 : ℝ) else 0) =
        (fun n => g n * (if (∏ i, rt i) ∣ n / R ∧ SieveTree.rough (rt (Fin.last k')) (n / R) then (1 : ℝ) else 0))
          (R * N) := by
    intro N _
    simp only [Nat.mul_div_cancel_left N hR]
  rw [Finset.sum_congr rfl e]
  refine (sum_Ioc_mul hR N₁ N₂ (fun n => g n *
    (if (∏ i, rt i) ∣ n / R ∧ SieveTree.rough (rt (Fin.last k')) (n / R) then (1 : ℝ) else 0))).trans ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : R ∣ n
  · rw [ite_eq_left h]
    congr 1
    exact if_congr (and_congr_left' (mul_dvd_iff_dvd_div hR h).symm) rfl rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (dvd_of_mul_right_dvd h'.1)), mul_zero]

omit [Route] in
/-- **The terms at a level on the multiples of `R`, as a sum over `n`.** -/
theorem famJR_eq (g : ℕ → ℝ) (N₁ N₂ z : ℕ) {R : ℕ} (hR : 0 < R) {k : ℕ} (F : Finset (Fin k → ℕ)) :
    famJR g N₁ N₂ z R F = ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂,
      g n * (if R * ∏ i, rt i ∣ n ∧ SieveTree.rough z (n / R) then 1 else 0) := by
  unfold famJR famJ
  refine Finset.sum_congr rfl fun rt _ => ?_
  have e : ∀ N ∈ Ioc (N₁ / R) (N₂ / R),
      g (R * N) * (if (∏ i, rt i) ∣ N ∧ SieveTree.rough z N then (1 : ℝ) else 0) =
        (fun n => g n * (if (∏ i, rt i) ∣ n / R ∧ SieveTree.rough z (n / R) then (1 : ℝ) else 0)) (R * N) := by
    intro N _
    simp only [Nat.mul_div_cancel_left N hR]
  rw [Finset.sum_congr rfl e]
  refine (sum_Ioc_mul hR N₁ N₂ (fun n => g n *
    (if (∏ i, rt i) ∣ n / R ∧ SieveTree.rough z (n / R) then (1 : ℝ) else 0))).trans ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : R ∣ n
  · rw [ite_eq_left h]
    congr 1
    exact if_congr (and_congr_left' (mul_dvd_iff_dvd_div hR h).symm) rfl rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (dvd_of_mul_right_dvd h'.1)), mul_zero]

/-! ### A frozen part -/

/-- The sum of `1/R` over a frozen part: the weight of the costs of its trees. -/
noncomputable def WF {ι : Type} (S : Finset ι) (R : ι → ℕ) : ℝ := ∑ i ∈ S, 1 / (R i : ℝ)

omit [Route] in
theorem WF_nonneg {ι : Type} (S : Finset ι) (R : ι → ℕ) : 0 ≤ WF S R :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The term of a chain's box over a frozen part, in `𝒜` minus the comparison set. -/
noncomputable def dIF (q : ℕ) (a : ZMod q) {ι : Type} (S : Finset ι) (R : ι → ℕ) {k' : ℕ}
    (bx : Fin (k' + 1) → Cell) : ℝ :=
  ∑ i ∈ S, (famIR (gA q a) (N1 q) (N2 q) (R i) (famB q bx) - famIR (gB q) (N1 q) (N2 q) (R i) (famB q bx))

/-- The terms at the floor `x^{f/DEN}` of a chain's box over a frozen part, in `𝒜` minus the comparison set. -/
noncomputable def dJF (q : ℕ) (a : ZMod q) (f : ℕ) {ι : Type} (S : Finset ι) (R : ι → ℕ) {k : ℕ}
    (bx : Fin k → Cell) : ℝ :=
  ∑ i ∈ S, (famJR (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (R i) (famB q bx) -
    famJR (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (R i) (famB q bx))

theorem dIF_cut {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {ι : Type} (S : Finset ι) (R : ι → ℕ) {k' : ℕ}
    (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ} (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) :
    dIF q a S R bx =
      dIF q a S R (Function.update bx i ((bx i).1, c)) + dIF q a S R (Function.update bx i (c, (bx i).2)) := by
  unfold dIF famIR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [famI_cutN _ _ _ hx bx i h1 h2, famI_cutN _ _ _ hx bx i h1 h2]
  ring

theorem dIF_buch {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {ι : Type} (S : Finset ι) (R : ι → ℕ) {k' : ℕ}
    (bx : Fin (k' + 1) → Cell) {f : ℕ} (hf : f ≤ (bx (Fin.last k')).1) :
    dIF q a S R bx = dJF q a f S R bx -
      dIF q a S R (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2)) := by
  unfold dIF dJF famIR famJR
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [famI_buchN _ _ _ hx bx hf, famI_buchN _ _ _ hx bx hf]
  ring

/-! ### The nodes of a tree over a frozen part -/

/-- The term of the chain's box over the frozen part, with its sign, is at least
`−(C·WF + o(1))x/(φ(q) log x)`. -/
def BdF {ι : Type} (S : ℕ → Finset ι) (R : ι → ℕ) (par : Bool) (C : ℝ) {k' : ℕ} (bx : Fin (k' + 1) → Cell) :
    Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    -((q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q)) ≤ sg par * dIF q a (S q) R bx

/-- The term of the chain's box over the frozen part is evaluated. -/
def EvIF {ι : Type} (S : ℕ → Finset ι) (R : ι → ℕ) {k' : ℕ} (bx : Fin (k' + 1) → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    |dIF q a (S q) R bx| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- The terms at the floor `x^{f/DEN}` of the chain's box over the frozen part are evaluated. -/
def EvJF {ι : Type} (S : ℕ → Finset ι) (R : ι → ℕ) (f : ℕ) {k : ℕ} (bx : Fin k → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    |dJF q a f (S q) R bx| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- A box that is evaluated. -/
theorem bdF_eval [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {par : Bool} {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (h : EvIF S R bx) : BdF S R par 0 bx := by
  intro η hη
  filter_upwards [h η hη] with q hq a ha
  have h1 := neg_abs_le_sg par (dIF q a (S q) R bx)
  have h2 := hq a ha
  rw [zero_mul, zero_add]
  linarith

/-- A larger cost. -/
theorem bdF_mono [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {par : Bool} {C C' : ℝ} {k' : ℕ}
    {bx : Fin (k' + 1) → Cell} (h : BdF S R par C bx) (hC : C ≤ C') : BdF S R par C' bx := by
  intro η hη
  filter_upwards [h η hη, big_ev] with q hq hbig a ha
  have hX := Xq_pos hbig
  have hW := WF_nonneg (S q) R
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have h1 : (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q) ≤
      (q.totient : ℝ)⁻¹ * ((C' * WF (S q) R + η) * Xq q) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (by linarith [mul_le_mul_of_nonneg_right hC hW]) hX.le) hφ
  linarith [hq a ha]

/-- A cut of a cell of the chain. -/
theorem bdF_split [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {par : Bool} {C₁ C₂ : ℝ} {k' : ℕ}
    (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ} (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2)
    (hl : BdF S R par C₁ (Function.update bx i ((bx i).1, c)))
    (hr : BdF S R par C₂ (Function.update bx i (c, (bx i).2))) : BdF S R par (C₁ + C₂) bx := by
  intro η hη
  filter_upwards [hl (η / 2) (by positivity), hr (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  rw [dIF_cut (by linarith) a (S q) R bx i h1 h2, mul_add]
  have e : (q.totient : ℝ)⁻¹ * (((C₁ + C₂) * WF (S q) R + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * ((C₁ * WF (S q) R + η / 2) * Xq q) +
        (q.totient : ℝ)⁻¹ * ((C₂ * WF (S q) R + η / 2) * Xq q) := by ring
  rw [e]
  linarith [hq1 a ha, hq2 a ha]

/-- Buchstab's identity on the chain at a floor whose terms are evaluated. -/
theorem bdF_buch [RouteOK] {ι : Type} {S : ℕ → Finset ι} {R : ι → ℕ} {par : Bool} {C : ℝ} {k' : ℕ}
    (bx : Fin (k' + 1) → Cell) {f : ℕ} (hf : f ≤ (bx (Fin.last k')).1) (hJ : EvJF S R f bx)
    (hc : BdF S R (!par) C (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))) : BdF S R par C bx := by
  intro η hη
  filter_upwards [hJ (η / 2) (by positivity), hc (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  rw [dIF_buch (by linarith) a (S q) R bx hf, mul_sub]
  have h1 := hq1 a ha
  have h2 := hq2 a ha
  rw [sg_not] at h2
  have h3 := neg_abs_le_sg par (dJF q a f (S q) R bx)
  have e : (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * ((C * WF (S q) R + η / 2) * Xq q) := by ring
  rw [e]
  linarith

end SieveAd

#print axioms SieveAd.famIR_eq
#print axioms SieveAd.famJR_eq
