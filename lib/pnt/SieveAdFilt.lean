/-
# A tree of Buchstab steps on the tuples of a box under a condition

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdTree.lean` treats the term of a box, the sum over all the tuples of the box. A reversed
term (`SieveAdRevDefs.lean`) is a sum over the tuples of a box whose first primes have their product in a range,
and its tree is made of the same steps. Here the steps are stated for the tuples of a box that satisfy a condition
`P`, with a weight `R q` on the costs:

* `famI_cutP`, `famI_buchP`: the cut of a cell and Buchstab's identity, as `SieveAd.famI_cut` and `famI_buch`,
  for the tuples that satisfy `P`; in Buchstab's identity the tuples with one more prime satisfy `P` on their
  first primes (`P ∘ Fin.init`).
* `dIP`, `dJP`: the term, and the terms at a floor, in `𝒜` minus the comparison set; `dIP_cut`, `dIP_buch`.
* `BdP P R par C bx`: the term, with its sign, is at least `−(C·R(q) + o(1))x/(φ(q) log x)`; `EvIP`, `EvJP`: the
  term, or the terms at a floor, are evaluated. `bdP_eval`, `bdP_split`, `bdP_buch`, `bdP_mono`: the nodes of a
  tree, in this form. `bd_iff`: `SieveAd.Bd` is the case of no condition and the weight `1`; `bd_split`, `bd_buch`,
  `bd_mono` are the nodes for `Bd`.
* `EvIX`, `EvJX`: the term of a box is evaluated under any two more atoms with thresholds as in
  `SieveLeaves.ThrOK`, uniformly in the atoms; `Tests.SoundX`: the tests are sound in that sense on the boxes of at
  most twelve primes. `EvIX.evIP`, `EvJX.evJP`: for atoms `E q` at each modulus.

The file imports `SieveAdTree.lean`.
-/
import SieveAdTree

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN K DEN_pos' K_pos')

variable [Route]

/-! ### The exact steps, under a condition -/

/-- **A cut, under a condition.** For `lo_i ≤ c ≤ hi_i`, the term of the tuples of a box that satisfy `P` is the
sum of the terms of those of the boxes with the cell `i` cut at `c`. -/
theorem famI_cutP (g : ℕ → ℝ) {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) (P : (Fin (k' + 1) → ℕ) → Prop) :
    famI g (N1 q) (N2 q) ((famB q bx).filter P) =
      famI g (N1 q) (N2 q) ((famB q (Function.update bx i ((bx i).1, c))).filter P) +
        famI g (N1 q) (N2 q) ((famB q (Function.update bx i (c, (bx i).2))).filter P) := by
  have e1 : (famB q (Function.update bx i ((bx i).1, c))).filter P =
      ((famB q bx).filter P).filter fun rt => (rt i : ℝ) < xq q ^ ((c : ℝ) / DEN) := by
    rw [famB_cut_lo hx bx i h2, Finset.filter_comm]
  have e2 : (famB q (Function.update bx i (c, (bx i).2))).filter P =
      ((famB q bx).filter P).filter fun rt => ¬ (rt i : ℝ) < xq q ^ ((c : ℝ) / DEN) := by
    rw [famB_cut_hi hx bx i h1, Finset.filter_comm]
  unfold famI
  rw [e1, e2, Finset.sum_filter_add_sum_filter_not]

/-- **Buchstab's identity on a box, under a condition.** With the floor `z = ⌈x^{f/DEN}⌉` for `f ≤ lo_last`: the
term of the tuples of the box that satisfy `P` is their `Σ S(A_r, z)` minus the term of the tuples of the box with
the cell `(f, hi_last)` for one more prime whose first primes satisfy `P`. -/
theorem famI_buchP (g : ℕ → ℝ) {q : ℕ} (hx : 1 ≤ xq q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) (P : (Fin (k' + 1) → ℕ) → Prop) :
    famI g (N1 q) (N2 q) ((famB q bx).filter P) =
      famJ g (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ ((famB q bx).filter P) -
        famI g (N1 q) (N2 q) ((famB q (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))).filter
          fun y => P (Fin.init y)) := by
  have hpt : ∀ rt ∈ (famB q bx).filter P, ∀ n ∈ Ioc (N1 q) (N2 q),
      g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0) =
        g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ n then 1 else 0) -
          ∑ p ∈ SieveTree.primesIco ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (rt (Fin.last k')),
            g n * (if (∏ i, (Fin.snoc rt p : Fin (k' + 2) → ℕ) i) ∣ n ∧
              SieveTree.rough ((Fin.snoc rt p : Fin (k' + 2) → ℕ) (Fin.last _)) n then 1 else 0) := by
    intro rt hrt n hn
    have hrt' := (Finset.mem_filter.1 hrt).1
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.1 hn).1; omega
    exact buch_pt_box hrt' (ceil_le_last hx hrt' hf) g hn0
  have hbij : ∀ G : (Fin (k' + 2) → ℕ) → ℝ,
      ∑ rt ∈ (famB q bx).filter P,
          ∑ p ∈ SieveTree.primesIco ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ (rt (Fin.last k')), G (Fin.snoc rt p) =
        ∑ y ∈ (famB q (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))).filter
          (fun y => P (Fin.init y)), G y := by
    intro G
    rw [Finset.sum_filter, Finset.sum_filter, ← famB_snoc_sum q bx f]
    refine Finset.sum_congr rfl fun rt _ => ?_
    by_cases h : P rt
    · simp only [Fin.init_snoc, h, ↓reduceIte]
    · simp only [Fin.init_snoc, h, ↓reduceIte, Finset.sum_const_zero]
  unfold famI famJ
  rw [Finset.sum_congr rfl fun rt hrt => Finset.sum_congr rfl (hpt rt hrt)]
  simp only [Finset.sum_sub_distrib]
  congr 1
  rw [← hbij]
  refine Finset.sum_congr rfl fun rt _ => ?_
  exact Finset.sum_comm

/-! ### The terms in `𝒜` minus the comparison set, under a condition -/

/-- The term of the tuples of a box that satisfy `P`, in `𝒜` minus the comparison set. -/
noncomputable def dIP (q : ℕ) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (P : (Fin (k' + 1) → ℕ) → Prop) : ℝ :=
  famI (gA q a) (N1 q) (N2 q) ((famB q bx).filter P) - famI (gB q) (N1 q) (N2 q) ((famB q bx).filter P)

/-- The terms `Σ S(·_r, ⌈x^{f/DEN}⌉)` of the tuples of a box that satisfy `P`, in `𝒜` minus the comparison set. -/
noncomputable def dJP (q : ℕ) (a : ZMod q) (f : ℕ) {k : ℕ} (bx : Fin k → Cell) (P : (Fin k → ℕ) → Prop) : ℝ :=
  famJ (gA q a) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ ((famB q bx).filter P) -
    famJ (gB q) (N1 q) (N2 q) ⌈xq q ^ ((f : ℝ) / DEN)⌉₊ ((famB q bx).filter P)

theorem dIP_true (q : ℕ) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) :
    dIP q a bx (fun _ => True) = dI q a bx := by
  unfold dIP dI
  rw [Finset.filter_true]

theorem dJP_true (q : ℕ) (a : ZMod q) (f : ℕ) {k : ℕ} (bx : Fin k → Cell) :
    dJP q a f bx (fun _ => True) = dJ q a f bx := by
  unfold dJP dJ
  rw [Finset.filter_true]

/-- Conditions that agree on the tuples of the box give the same term. -/
theorem dIP_congr {q : ℕ} {a : ZMod q} {k' : ℕ} {bx : Fin (k' + 1) → Cell} {P P' : (Fin (k' + 1) → ℕ) → Prop}
    (h : ∀ rt ∈ famB q bx, P rt ↔ P' rt) : dIP q a bx P = dIP q a bx P' := by
  unfold dIP
  rw [Finset.filter_congr h]

/-- Conditions that agree on the tuples of the box give the same terms at a floor. -/
theorem dJP_congr {q : ℕ} {a : ZMod q} {f : ℕ} {k : ℕ} {bx : Fin k → Cell} {P P' : (Fin k → ℕ) → Prop}
    (h : ∀ rt ∈ famB q bx, P rt ↔ P' rt) : dJP q a f bx P = dJP q a f bx P' := by
  unfold dJP
  rw [Finset.filter_congr h]

theorem dIP_cut {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) (P : (Fin (k' + 1) → ℕ) → Prop) :
    dIP q a bx P =
      dIP q a (Function.update bx i ((bx i).1, c)) P + dIP q a (Function.update bx i (c, (bx i).2)) P := by
  unfold dIP
  rw [famI_cutP (gA q a) hx bx i h1 h2 P, famI_cutP (gB q) hx bx i h1 h2 P]
  ring

theorem dIP_buch {q : ℕ} (hx : 1 ≤ xq q) (a : ZMod q) {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) (P : (Fin (k' + 1) → ℕ) → Prop) :
    dIP q a bx P = dJP q a f bx P -
      dIP q a (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2)) (fun y => P (Fin.init y)) := by
  unfold dIP dJP
  rw [famI_buchP (gA q a) hx bx hf P, famI_buchP (gB q) hx bx hf P]
  ring

/-! ### The nodes of a tree, under a condition and with a weight -/

/-- The term of the tuples of the box that satisfy `P q`, with its sign, is at least
`−(C·R(q) + o(1))x/(φ(q) log x)`. -/
def BdP {k' : ℕ} (P : ∀ _ : ℕ, (Fin (k' + 1) → ℕ) → Prop) (R : ℕ → ℝ) (par : Bool) (C : ℝ)
    (bx : Fin (k' + 1) → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    -((q.totient : ℝ)⁻¹ * ((C * R q + η) * Xq q)) ≤ sg par * dIP q a bx (P q)

/-- The term of the tuples of the box that satisfy `P q` is evaluated. -/
def EvIP {k' : ℕ} (P : ∀ _ : ℕ, (Fin (k' + 1) → ℕ) → Prop) (bx : Fin (k' + 1) → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    |dIP q a bx (P q)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- The terms at the floor `x^{f/DEN}` of the tuples of the box that satisfy `P q` are evaluated. -/
def EvJP {k : ℕ} (P : ∀ _ : ℕ, (Fin k → ℕ) → Prop) (f : ℕ) (bx : Fin k → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a →
    |dJP q a f bx (P q)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- `Bd` is `BdP` with no condition and the weight `1`. -/
theorem bd_iff {par : Bool} {C : ℝ} {k' : ℕ} {bx : Fin (k' + 1) → Cell} :
    Bd par C bx ↔ BdP (fun _ _ => True) (fun _ => 1) par C bx := by
  unfold Bd BdP
  simp only [dIP_true, mul_one]

/-- `EvJ` is `EvJP` with no condition. -/
theorem evJ_iff {f : ℕ} {k : ℕ} {bx : Fin k → Cell} : EvJ f bx ↔ EvJP (fun _ _ => True) f bx := by
  unfold EvJ EvJP
  simp only [dJP_true]

/-- A box that is evaluated. -/
theorem bdP_eval [RouteOK] {k' : ℕ} {P : ∀ _ : ℕ, (Fin (k' + 1) → ℕ) → Prop} {R : ℕ → ℝ} {par : Bool}
    {bx : Fin (k' + 1) → Cell} (h : EvIP P bx) : BdP P R par 0 bx := by
  intro η hη
  filter_upwards [h η hη] with q hq a ha
  have h1 := neg_abs_le_sg par (dIP q a bx (P q))
  have h2 := hq a ha
  rw [zero_mul, zero_add]
  linarith

/-- A larger cost, for a nonnegative weight. -/
theorem bdP_mono [RouteOK] {k' : ℕ} {P : ∀ _ : ℕ, (Fin (k' + 1) → ℕ) → Prop} {R : ℕ → ℝ} {par : Bool} {C C' : ℝ}
    {bx : Fin (k' + 1) → Cell} (hR : ∀ᶠ q : ℕ in atTop, 0 ≤ R q) (h : BdP P R par C bx) (hC : C ≤ C') :
    BdP P R par C' bx := by
  intro η hη
  filter_upwards [h η hη, hR, big_ev] with q hq hRq hbig a ha
  have hX := Xq_pos hbig
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by positivity
  have h1 : (q.totient : ℝ)⁻¹ * ((C * R q + η) * Xq q) ≤ (q.totient : ℝ)⁻¹ * ((C' * R q + η) * Xq q) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (by linarith [mul_le_mul_of_nonneg_right hC hRq]) hX.le) hφ
  linarith [hq a ha]

/-- A cut of a cell. -/
theorem bdP_split [RouteOK] {k' : ℕ} {P : ∀ _ : ℕ, (Fin (k' + 1) → ℕ) → Prop} {R : ℕ → ℝ} {par : Bool}
    {C₁ C₂ : ℝ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ} (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2)
    (hl : BdP P R par C₁ (Function.update bx i ((bx i).1, c)))
    (hr : BdP P R par C₂ (Function.update bx i (c, (bx i).2))) : BdP P R par (C₁ + C₂) bx := by
  intro η hη
  filter_upwards [hl (η / 2) (by positivity), hr (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  rw [dIP_cut (by linarith) a bx i h1 h2, mul_add]
  have e : (q.totient : ℝ)⁻¹ * (((C₁ + C₂) * R q + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * ((C₁ * R q + η / 2) * Xq q) + (q.totient : ℝ)⁻¹ * ((C₂ * R q + η / 2) * Xq q) := by ring
  rw [e]
  linarith [hq1 a ha, hq2 a ha]

/-- Buchstab's identity at a floor whose terms are evaluated. -/
theorem bdP_buch [RouteOK] {k' : ℕ} {P : ∀ _ : ℕ, (Fin (k' + 1) → ℕ) → Prop} {R : ℕ → ℝ} {par : Bool} {C : ℝ}
    (bx : Fin (k' + 1) → Cell) {f : ℕ} (hf : f ≤ (bx (Fin.last k')).1) (hJ : EvJP P f bx)
    (hc : BdP (fun q y => P q (Fin.init y)) R (!par) C
      (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))) : BdP P R par C bx := by
  intro η hη
  filter_upwards [hJ (η / 2) (by positivity), hc (η / 2) (by positivity), big_ev] with q hq1 hq2 hbig a ha
  obtain ⟨-, hx3, -⟩ := big_facts hbig
  rw [dIP_buch (by linarith) a bx hf, mul_sub]
  have h1 := hq1 a ha
  have h2 := hq2 a ha
  rw [sg_not] at h2
  have h3 := neg_abs_le_sg par (dJP q a f bx (P q))
  have e : (q.totient : ℝ)⁻¹ * ((C * R q + η) * Xq q) =
      (q.totient : ℝ)⁻¹ * (η / 2 * Xq q) + (q.totient : ℝ)⁻¹ * ((C * R q + η / 2) * Xq q) := by ring
  rw [e]
  linarith

/-- A larger cost. -/
theorem bd_mono [RouteOK] {par : Bool} {C C' : ℝ} {k' : ℕ} {bx : Fin (k' + 1) → Cell} (h : Bd par C bx)
    (hC : C ≤ C') : Bd par C' bx :=
  bd_iff.2 (bdP_mono (Filter.Eventually.of_forall fun _ => zero_le_one) (bd_iff.1 h) hC)

/-- A cut of a cell. -/
theorem bd_split [RouteOK] {par : Bool} {C₁ C₂ : ℝ} {k' : ℕ} (bx : Fin (k' + 1) → Cell) (i : Fin (k' + 1)) {c : ℕ}
    (h1 : (bx i).1 ≤ c) (h2 : c ≤ (bx i).2) (hl : Bd par C₁ (Function.update bx i ((bx i).1, c)))
    (hr : Bd par C₂ (Function.update bx i (c, (bx i).2))) : Bd par (C₁ + C₂) bx :=
  bd_iff.2 (bdP_split bx i h1 h2 (bd_iff.1 hl) (bd_iff.1 hr))

/-- Buchstab's identity at a floor whose terms are evaluated. -/
theorem bd_buch [RouteOK] {par : Bool} {C : ℝ} {k' : ℕ} (bx : Fin (k' + 1) → Cell) {f : ℕ}
    (hf : f ≤ (bx (Fin.last k')).1) (hJ : EvJ f bx)
    (hc : Bd (!par) C (Fin.snoc (α := fun _ => Cell) bx (f, (bx (Fin.last k')).2))) : Bd par C bx :=
  bd_iff.2 (bdP_buch bx hf (evJ_iff.1 hJ) (bd_iff.1 hc))

/-! ### Tests that are sound under two more atoms -/

/-- The term of the box is evaluated under any two more atoms, uniformly in the atoms. -/
def EvIX {k' : ℕ} (bx : Fin (k' + 1) → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom (k' + 1)), E.length ≤ 2 →
    ThrOK q E → |dIP q a bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- The terms of the box at the floor `x^{f/DEN}` are evaluated under any two more atoms, uniformly in the atoms. -/
def EvJX {k : ℕ} (f : ℕ) (bx : Fin k → Cell) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ q : ℕ in atTop, ∀ a : ZMod q, IsUnit a → ∀ E : List (Atom k), E.length ≤ 2 →
    ThrOK q E → |dJP q a f bx (fun rt => ∀ A ∈ E, A.sem rt)| ≤ (q.totient : ℝ)⁻¹ * (η * Xq q)

/-- **The tests are sound under two more atoms**, on the boxes of at most twelve primes. -/
structure Tests.SoundX (τ : Tests) : Prop where
  soundI : ∀ (bl : List Cell) (cfg : Cfg) (k' : ℕ) (h : bl.length = k' + 1), k' + 1 ≤ 12 → τ.okI bl cfg = true →
    EvIX (boxFn bl (k' + 1) h)
  soundJ : ∀ (bl : List Cell) (f : ℕ) (cfg : Cfg) (k : ℕ) (h : bl.length = k), k ≤ 12 → τ.okJ bl f cfg = true →
    EvJX f (boxFn bl k h)

/-- With two atoms at each modulus, whose thresholds are as in `ThrOK` for large `q`. -/
theorem EvIX.evIP {k' : ℕ} {bx : Fin (k' + 1) → Cell} (h : EvIX bx) (E : ∀ _ : ℕ, List (Atom (k' + 1)))
    (hE : ∀ q, (E q).length ≤ 2) (hthr : ∀ᶠ q : ℕ in atTop, ThrOK q (E q)) :
    EvIP (fun q rt => ∀ A ∈ E q, A.sem rt) bx := by
  intro η hη
  filter_upwards [h η hη, hthr] with q hq ht a ha
  exact hq a ha (E q) (hE q) ht

theorem EvJX.evJP {k : ℕ} {f : ℕ} {bx : Fin k → Cell} (h : EvJX f bx) (E : ∀ _ : ℕ, List (Atom k))
    (hE : ∀ q, (E q).length ≤ 2) (hthr : ∀ᶠ q : ℕ in atTop, ThrOK q (E q)) :
    EvJP (fun q rt => ∀ A ∈ E q, A.sem rt) f bx := by
  intro η hη
  filter_upwards [h η hη, hthr] with q hq ht a ha
  exact hq a ha (E q) (hE q) ht

end SieveAd

#print axioms SieveAd.bdP_split
#print axioms SieveAd.bdP_buch
#print axioms SieveAd.bd_split
#print axioms SieveAd.bd_buch
