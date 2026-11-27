import PathBasis

/-!
# The path basis (T2 (i), (iii)): the straightening machinery

The tools for the straightening law of the path polynomials `Ψ(P, I)` of `PathBasis`, in column coordinates: the column
`c` of a filling is `col(c) = I(c)` for `c ≥ 1` and `I(c)ᶜ` for `c ≤ 0`, and its state starts at `[col = ∅]` resp.
`[col = univ]`, is wedged with the letter vector when the height grows and contracted when it drops (`colS`). A path is
read through its column heights (`HPath`, window `[−T, T]`); `Ψ(P, C) = ∏_c S_c(C(c))` (`psi`).

**Main results.**
* *The Garnir sums of two states* `gar_p(S, T)(X, Y) = Σ_{U ⊆ X, |U| = p} ±S(U)·T((X ∖ U) ∪ Y)` (the coordinates of
  `Σ (S ∧ T₍₁₎) ⊗ T₍₂₎`) under one more letter (`gar_wedge_left`, `gar_wedge_right`, `gar_contr_left`,
  `gar_contr_right`): a signed sum of Garnir sums of the old states, plus, when one element is shuffled, a product of
  states with the step moved to the other column.
* *The order and the lower part*: paths are ordered lexicographically by the potentials `Σ_c wt(h_t(c))`
  (`HPath.lt`, well founded); `lower P` is the `ℤ`-span of all `Ψ(Q, C)`, `Q ≺ P`, `C` any filling. A monomial of the
  new letter carries the lower part of the truncation into the lower part (`mono_mul_lower`, the first-row trick);
  the stepped columns expand into such monomials (`stepProd_mem`).
* *Exchange and symmetry from the Garnir relations* (Möbius inversion on subsets): `exch_sub_mem`, `symm_sub_mem`,
  and for paths satisfying the Garnir relations (`GarStmt`) `HPath.exch_mem`, `HPath.symm_mem`.
* *The special configurations*: a step moved across equal columns (`conf_move`, `conf_move_iff`), valid
  configurations are lower paths (`conf_mem_lower_of_valid_vec`, `conf_mem_lower_of_valid_cov`), and the cascades
  through the equal columns on both sides (`special_vec`, `special_cov`).

**Not here.** The assembly: the induction `GarStmt P.trunc → GarStmt P` combining the four state lemmas (seven cases;
the special cases are `special_vec` and `special_cov`, the doubly stepped ones vanish by `wedge_wedge_self` and
`contr_contr_self`), the straightening of a non-standard filling by `HPath.exch_mem` with `D = col(c+1)_{<t} ∖ col(c)`
(each exchanged term raises `col(c + 1)` in the colex order), the spanning of the multidegree-`B` polynomials (first-row
trick), the translation to `PathBasis.pathFam` (heights to weights, column to `I` coordinates), and the basis over every
commutative ring from `PathBasis.card_pathIdx`.
-/

namespace PathSpan

open MvPolynomial Finset TwistedDegree PathBasis

noncomputable section

/-! ## Inversion signs and the Garnir sums of two column states -/

section Gar

variable {A : Type*} [CommRing A] {n : ℕ}

/-- **The inversion count** `#{(a, b) ∈ U × V : b < a}`. -/
def inv (U V : Finset (Fin n)) : ℕ := ∑ a ∈ U, (V.filter (· < a)).card

/-- **The inversion sign** `(−1)^{#{(a, b) ∈ U × V : b < a}}` (no disjointness is assumed). -/
def sgn (U V : Finset (Fin n)) : A := (-1) ^ inv U V

/-- **Signs of equal parity agree.** -/
theorem neg_one_pow_congr {a b : ℕ} (h : a % 2 = b % 2) : ((-1 : A) ^ a) = (-1) ^ b := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, h, pow_add, pow_add, pow_mul, pow_mul]
  simp

/-- **Signs of opposite parity cancel.** -/
theorem neg_one_pow_add_eq_zero {a b : ℕ} (h : (a + 1) % 2 = b % 2) : ((-1 : A) ^ a) + (-1) ^ b = 0 := by
  rw [← neg_one_pow_congr h, pow_succ]
  ring

/-- **The inversion count with one more left entry.** -/
theorem inv_insert_left {u : Fin n} {U : Finset (Fin n)} (hu : u ∉ U) (V : Finset (Fin n)) :
    inv (insert u U) V = inv U V + (V.filter (· < u)).card := by
  rw [inv, sum_insert hu, inv, add_comm]

/-- **The inversion count with one more right entry.** -/
theorem inv_insert_right (U : Finset (Fin n)) {v : Fin n} {V : Finset (Fin n)} (hv : v ∉ V) :
    inv U (insert v V) = inv U V + (U.filter (v < ·)).card := by
  rw [inv, inv, card_filter, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp [hv])]
  · rfl

/-- **The inversion count with the empty set.** -/
@[simp] theorem inv_empty_left (V : Finset (Fin n)) : inv ∅ V = 0 := by simp [inv]

/-- **The inversion count with the empty set.** -/
@[simp] theorem inv_empty_right (U : Finset (Fin n)) : inv U ∅ = 0 := by simp [inv]

/-- **The Garnir sum** of two column states `S` (degree `p`) and `T`: the coordinate at `(X, Y)` of
`Σ (S ∧ T₍₁₎) ⊗ T₍₂₎`, i.e. `Σ_{U ⊆ X, |U| = p} sgn(U, X ∖ U)·sgn(X ∖ U, Y)·S(U)·T((X ∖ U) ∪ Y)`. With `|X| = p`
it is the product `S(X)·T(Y)` (`gar_self`). -/
def gar (p : ℕ) (S T : Finset (Fin n) → A) (X Y : Finset (Fin n)) : A :=
  ∑ U ∈ X.powersetCard p, sgn (X \ U) Y * sgn U (X \ U) * S U * T ((X \ U) ∪ Y)

/-- **The Garnir sum with nothing to shuffle** is the product. -/
theorem gar_self (p : ℕ) (S T : Finset (Fin n) → A) {X : Finset (Fin n)} (hX : X.card = p)
    (Y : Finset (Fin n)) : gar p S T X Y = S X * T Y := by
  rw [gar, ← hX, powersetCard_self, sum_singleton, sdiff_self]
  simp [sgn, inv]

/-- **A filter count splits** at an element `u ∉ s` into the parts below and above. -/
theorem card_lt_add_card_gt {s : Finset (Fin n)} {u : Fin n} (hu : u ∉ s) :
    (s.filter (· < u)).card + (s.filter (u < ·)).card = s.card := by
  rw [← card_union_of_disjoint (disjoint_filter.2 fun x _ h1 h2 => lt_asymm h1 h2)]
  congr 1
  ext x
  simp only [mem_union, mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hx
    rcases lt_trichotomy x u with h | h | h
    · exact Or.inl ⟨hx, h⟩
    · exact absurd (h ▸ hx) hu
    · exact Or.inr ⟨hx, h⟩

/-- **A filter count over a disjoint union.** -/
theorem card_filter_union {s t : Finset (Fin n)} (h : Disjoint s t) (P : Fin n → Prop) [DecidablePred P] :
    ((s ∪ t).filter P).card = (s.filter P).card + (t.filter P).card := by
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

/-- **(W1) Wedging the left state**: `gar_{p+1}(y ∧ S, T)(X, Y) = Σ_{u ∈ X} ±y_u·gar_p(S, T)(X ∖ u, Y)`, the sign
being `(−1)^{p + #{x ∈ X : x < u}}`. -/
theorem gar_wedge_left (p : ℕ) (y : Fin n → A) (S T : Finset (Fin n) → A) (X Y : Finset (Fin n)) :
    gar (p + 1) (wedge y S) T X Y =
      ∑ u ∈ X, (-1) ^ (p + (X.filter (· < u)).card) * y u * gar p S T (X.erase u) Y := by
  simp only [gar, wedge, mul_sum, sum_mul]
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1.erase x.2⟩) (fun x => ⟨insert x.1 x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨U, u⟩ hx
    simp only [mem_sigma, mem_powersetCard] at hx ⊢
    obtain ⟨⟨hUX, hU⟩, hu⟩ := hx
    refine ⟨hUX hu, erase_subset_erase u hUX, ?_⟩
    rw [card_erase_of_mem hu, hU, Nat.add_sub_cancel]
  · rintro ⟨u, U⟩ hx
    simp only [mem_sigma, mem_powersetCard] at hx ⊢
    obtain ⟨hu, hUX, hU⟩ := hx
    have huU : u ∉ U := fun h => (notMem_erase u X) (hUX h)
    refine ⟨⟨insert_subset hu (hUX.trans (erase_subset u X)), ?_⟩, mem_insert_self u U⟩
    rw [card_insert_of_notMem huU, hU]
  · rintro ⟨U, u⟩ hx
    simp only [mem_sigma] at hx
    simp [insert_erase hx.2]
  · rintro ⟨u, U⟩ hx
    simp only [mem_sigma, mem_powersetCard] at hx
    have huU : u ∉ U := fun h => (notMem_erase u X) (hx.2.1 h)
    simp [erase_insert huU]
  · rintro ⟨U, u⟩ hx
    simp only [mem_sigma, mem_powersetCard] at hx
    obtain ⟨⟨hUX, hU⟩, hu⟩ := hx
    simp only
    have hW : X \ U = X.erase u \ U.erase u := by
      ext x
      simp only [mem_sdiff, mem_erase]
      constructor
      · rintro ⟨hx, hxU⟩
        exact ⟨⟨fun h => hxU (h ▸ hu), hx⟩, fun h => hxU h.2⟩
      · rintro ⟨⟨hxu, hx⟩, hxU⟩
        exact ⟨hx, fun h => hxU ⟨hxu, h⟩⟩
    rw [← hW]
    -- the sign identity
    have hsgn : (sgn U (X \ U) : A) * sg u U = (-1) ^ (p + (X.filter (· < u)).card) * sgn (U.erase u) (X \ U) := by
      have hue : u ∉ U.erase u := notMem_erase u U
      have hinv : inv U (X \ U) = inv (U.erase u) (X \ U) + ((X \ U).filter (· < u)).card := by
        have := inv_insert_left hue (X \ U)
        rwa [insert_erase hu] at this
      have hsg : (sg u U : A) = (-1) ^ ((U.erase u).filter (u < ·)).card := by
        rw [sg]
        congr 2
        ext x
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨hx, h⟩
          exact ⟨⟨(ne_of_lt h).symm, hx⟩, h⟩
        · rintro ⟨⟨_, hx⟩, h⟩
          exact ⟨hx, h⟩
      have hsplit := card_lt_add_card_gt hue
      have hX : (X.filter (· < u)).card = ((X \ U).filter (· < u)).card + ((U.erase u).filter (· < u)).card := by
        have hXd : X = (X \ U) ∪ (U.erase u) ∪ {u} := by
          ext x
          simp only [mem_union, mem_sdiff, mem_erase, mem_singleton]
          constructor
          · intro hx
            by_cases hxU : x ∈ U
            · by_cases hxu : x = u
              · exact Or.inr hxu
              · exact Or.inl (Or.inr ⟨hxu, hxU⟩)
            · exact Or.inl (Or.inl ⟨hx, hxU⟩)
          · rintro ((⟨hx, _⟩ | ⟨_, hx⟩) | rfl)
            · exact hx
            · exact hUX hx
            · exact hUX hu
        have hd1 : Disjoint (X \ U) (U.erase u) :=
          disjoint_left.2 fun x h1 h2 => (mem_sdiff.1 h1).2 (mem_of_mem_erase h2)
        have hd2 : Disjoint ((X \ U) ∪ U.erase u) {u} := by
          rw [disjoint_singleton_right, mem_union, not_or]
          exact ⟨fun h => (mem_sdiff.1 h).2 hu, notMem_erase u U⟩
        conv_lhs => rw [hXd]
        rw [card_filter_union hd2, card_filter_union hd1]
        simp
      have hcard : (U.erase u).card = p := by rw [card_erase_of_mem hu, hU, Nat.add_sub_cancel]
      rw [sgn, sgn, hinv, hsg, ← pow_add, ← pow_add]
      refine neg_one_pow_congr ?_
      omega
    calc sgn (X \ U) Y * sgn U (X \ U) * (sg u U * y u * S (U.erase u)) * T ((X \ U) ∪ Y)
        = sgn (X \ U) Y * (sgn U (X \ U) * sg u U) * y u * S (U.erase u) * T ((X \ U) ∪ Y) := by ring
      _ = _ := by rw [hsgn]; ring

/-- **The inversion count over a disjoint union on the left.** -/
theorem inv_union_left {U U' : Finset (Fin n)} (h : Disjoint U U') (V : Finset (Fin n)) :
    inv (U ∪ U') V = inv U V + inv U' V := by
  rw [inv, sum_union h, inv, inv]

/-- **The inversion count over a disjoint union on the right.** -/
theorem inv_union_right (U : Finset (Fin n)) {V V' : Finset (Fin n)} (h : Disjoint V V') :
    inv U (V ∪ V') = inv U V + inv U V' := by
  rw [inv, inv, inv, ← sum_add_distrib]
  exact sum_congr rfl fun a _ => card_filter_union h _

/-- **The inversion count with a single left entry.** -/
theorem inv_singleton_left (a : Fin n) (V : Finset (Fin n)) : inv {a} V = (V.filter (· < a)).card := by
  rw [inv, sum_singleton]

/-- **The inversion count with a single right entry.** -/
theorem inv_singleton_right (U : Finset (Fin n)) (b : Fin n) : inv U {b} = (U.filter (b < ·)).card := by
  have := inv_insert_right U (V := ∅) (notMem_empty b)
  simpa using this

/-- **`sg` is an inversion sign**: `sg a J = sgn J {a}`. -/
theorem sg_eq_sgn (a : Fin n) (J : Finset (Fin n)) : (sg a J : A) = sgn J {a} := by
  rw [sg, sgn, inv_singleton_right]

/-- **A state of degree `h`**: it vanishes off the sets of size `h`. -/
def IsDeg (S : Finset (Fin n) → A) (h : ℕ) : Prop := ∀ J : Finset (Fin n), J.card ≠ h → S J = 0

/-- **Wedging raises the degree by one.** -/
theorem IsDeg.wedge {S : Finset (Fin n) → A} {h : ℕ} (hS : IsDeg S h) (y : Fin n → A) :
    IsDeg (TwistedDegree.wedge y S) (h + 1) := fun _ hJ => wedge_supp hS y hJ

/-- **Contracting lowers the degree by one.** -/
theorem IsDeg.contr {S : Finset (Fin n) → A} {h : ℕ} (hS : IsDeg S (h + 1)) (y : Fin n → A) :
    IsDeg (TwistedDegree.contr y S) h := fun _ hJ => contr_supp hS y (by omega)

/-- **The parts of a set split by a subset.** -/
theorem card_sdiff_add {U X : Finset (Fin n)} (h : U ⊆ X) : (X \ U).card + U.card = X.card := by
  rw [card_sdiff_of_subset h]
  have := card_le_card h
  omega

/-- **The union of two sets is smaller than the sum when they meet.** -/
theorem card_union_lt {W Y : Finset (Fin n)} (h : ¬ Disjoint W Y) : (W ∪ Y).card < W.card + Y.card := by
  rw [← card_union_add_card_inter]
  have : 0 < (W ∩ Y).card := card_pos.2 (not_disjoint_iff_nonempty_inter.1 h)
  omega

/-- **(W2) Wedging the right state**: with `|X| + |Y| = p + q + 1` and `T` of degree `q`,
`gar_p(S, y ∧ T)(X, Y) = Σ_{v ∈ Y} sg(v, Y)·y_v·gar_p(S, T)(X, Y ∖ v) + Σ_{v ∈ X} ±y_v·gar_p(S, T)(X ∖ v, Y)`, the
second sign being `(−1)^{|Y| + #{x ∈ X : v < x}}`. -/
theorem gar_wedge_right (p : ℕ) {q : ℕ} (y : Fin n → A) (S : Finset (Fin n) → A) {T : Finset (Fin n) → A}
    (hT : IsDeg T q) {X Y : Finset (Fin n)} (hXY : X.card + Y.card = p + q + 1) :
    gar p S (wedge y T) X Y =
      ∑ v ∈ Y, sg v Y * y v * gar p S T X (Y.erase v) +
        ∑ v ∈ X, (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v * gar p S T (X.erase v) Y := by
  -- reindex the second sum over the pairs `(U, v)` with `v ∈ X \ U`
  have h2 : ∑ v ∈ X, (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v * gar p S T (X.erase v) Y =
      ∑ U ∈ X.powersetCard p, ∑ v ∈ X \ U, (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v *
        (sgn ((X \ U).erase v) Y * sgn U ((X \ U).erase v) * S U * T (((X \ U).erase v) ∪ Y)) := by
    simp only [gar, mul_sum]
    rw [sum_sigma', sum_sigma']
    refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨v, U⟩ hx
      simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hx ⊢
      exact ⟨⟨hx.2.1.trans (erase_subset v X), hx.2.2⟩, hx.1, fun h => notMem_erase v X (hx.2.1 h)⟩
    · rintro ⟨U, v⟩ hx
      simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hx ⊢
      exact ⟨hx.2.1, fun a ha => mem_erase.2 ⟨fun h => hx.2.2 (h ▸ ha), hx.1.1 ha⟩, hx.1.2⟩
    · rintro ⟨v, U⟩ _; rfl
    · rintro ⟨U, v⟩ _; rfl
    · rintro ⟨v, U⟩ hx
      simp only [mem_sigma, mem_powersetCard] at hx
      have e : X.erase v \ U = (X \ U).erase v := by
        ext x; simp only [mem_sdiff, mem_erase]; tauto
      simp only [e]
  rw [h2]
  simp only [gar, mul_sum]
  rw [sum_comm (s := Y)]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun U hU => ?_
  rw [mem_powersetCard] at hU
  obtain ⟨hUX, hUc⟩ := hU
  have hW : (X \ U).card + Y.card = q + 1 := by
    have := card_sdiff_add hUX
    omega
  set W := X \ U with hWdef
  -- the left side: expand the wedge
  by_cases hd : Disjoint W Y
  · rw [wedge, sum_union hd, mul_add, mul_sum, mul_sum, add_comm]
    congr 1
    · -- `v ∈ Y`
      refine sum_congr rfl fun v hv => ?_
      have hvW : v ∉ W := fun h => disjoint_left.1 hd h hv
      have e1 : (W ∪ Y).erase v = W ∪ Y.erase v := by
        rw [erase_union_distrib, erase_eq_of_notMem hvW]
      have e2 : X \ U = W := rfl
      rw [e1]
      have hsgn : (sgn W Y : A) * sg v (W ∪ Y) = sg v Y * sgn W (Y.erase v) := by
        have hYe : Y = insert v (Y.erase v) := (insert_erase hv).symm
        have hve : v ∉ Y.erase v := notMem_erase v Y
        have i1 : inv W Y = inv W (Y.erase v) + (W.filter (v < ·)).card := by
          have := inv_insert_right W hve; rwa [← hYe] at this
        have i3 : ((W ∪ Y).filter (v < ·)).card = (W.filter (v < ·)).card + (Y.filter (v < ·)).card :=
          card_filter_union hd _
        rw [sgn, sgn, sg, sg, i1, i3, ← pow_add, ← pow_add]
        refine neg_one_pow_congr ?_
        omega
      calc sgn W Y * sgn U W * S U * (sg v (W ∪ Y) * y v * T (W ∪ Y.erase v))
          = (sgn W Y * sg v (W ∪ Y)) * sgn U W * y v * S U * T (W ∪ Y.erase v) := by ring
        _ = _ := by rw [hsgn]; ring
    · -- `v ∈ W`
      refine sum_congr rfl fun v hv => ?_
      have hvY : v ∉ Y := disjoint_left.1 hd hv
      have hvU : v ∉ U := (mem_sdiff.1 hv).2
      have e1 : (W ∪ Y).erase v = W.erase v ∪ Y := by
        rw [erase_union_distrib, erase_eq_of_notMem hvY]
      rw [e1]
      have hsgn : (sgn W Y : A) * sgn U W * sg v (W ∪ Y) =
          (-1) ^ (Y.card + (X.filter (v < ·)).card) * (sgn (W.erase v) Y * sgn U (W.erase v)) := by
        have hWe : W = insert v (W.erase v) := (insert_erase hv).symm
        have hve : v ∉ W.erase v := notMem_erase v W
        have i1 : inv W Y = inv (W.erase v) Y + (Y.filter (· < v)).card := by
          have := inv_insert_left hve Y; rwa [← hWe] at this
        have i2 : inv U W = inv U (W.erase v) + (U.filter (v < ·)).card := by
          have := inv_insert_right U hve; rwa [← hWe] at this
        have i3 : ((W ∪ Y).filter (v < ·)).card = ((W.erase v).filter (v < ·)).card + (Y.filter (v < ·)).card := by
          conv_lhs => rw [hWe, insert_union, filter_insert]
          simp only [lt_irrefl, ↓reduceIte]
          exact card_filter_union (P := (v < ·))
            (disjoint_left.2 fun x hx hxY => disjoint_left.1 hd (mem_of_mem_erase hx) hxY)
        have i4 := card_lt_add_card_gt hvY
        have hXs : X = U ∪ W.erase v ∪ {v} := by
          ext x; simp only [mem_union, mem_singleton, mem_erase, W, mem_sdiff]
          constructor
          · intro hx; by_cases h1 : x ∈ U
            · exact Or.inl (Or.inl h1)
            · by_cases h2 : x = v
              · exact Or.inr h2
              · exact Or.inl (Or.inr ⟨h2, hx, h1⟩)
          · rintro ((h | ⟨_, h, _⟩) | rfl)
            · exact hUX h
            · exact h
            · exact (mem_sdiff.1 hv).1
        have i5 : (X.filter (v < ·)).card = (U.filter (v < ·)).card + ((W.erase v).filter (v < ·)).card := by
          have d1 : Disjoint U (W.erase v) :=
            disjoint_left.2 fun x hx h => (mem_sdiff.1 (mem_of_mem_erase h)).2 hx
          have d2 : Disjoint (U ∪ W.erase v) {v} := by
            rw [disjoint_singleton_right, mem_union, not_or]; exact ⟨hvU, notMem_erase v W⟩
          conv_lhs => rw [hXs]
          rw [card_filter_union d2, card_filter_union d1]
          simp
        rw [sgn, sgn, sgn, sgn, sg, i1, i2, i3, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        refine neg_one_pow_congr ?_
        omega
      calc sgn W Y * sgn U W * S U * (sg v (W ∪ Y) * y v * T (W.erase v ∪ Y))
          = (sgn W Y * sgn U W * sg v (W ∪ Y)) * y v * S U * T (W.erase v ∪ Y) := by ring
        _ = _ := by rw [hsgn]; ring
  · -- `W` meets `Y`: the left side vanishes, the right side cancels in pairs
    have hL : wedge y T (W ∪ Y) = 0 := (hT.wedge y) _ (by have := card_union_lt hd; omega)
    rw [hL, mul_zero]
    have hY : ∀ v ∈ Y, v ∉ W → sg v Y * y v * (sgn W (Y.erase v) * sgn U W * S U * T (W ∪ Y.erase v)) = 0 := by
      intro v hv hvW
      have : ¬ Disjoint W (Y.erase v) := by
        rw [not_disjoint_iff] at hd ⊢
        obtain ⟨x, hxW, hxY⟩ := hd
        exact ⟨x, hxW, mem_erase.2 ⟨fun h => hvW (h ▸ hxW), hxY⟩⟩
      have hYp := card_pos.2 ⟨v, hv⟩
      rw [hT _ (by have := card_union_lt this; rw [card_erase_of_mem hv] at this; omega)]
      ring
    have hX : ∀ v ∈ W, v ∉ Y → (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v *
        (sgn (W.erase v) Y * sgn U (W.erase v) * S U * T (W.erase v ∪ Y)) = 0 := by
      intro v hv hvY
      have : ¬ Disjoint (W.erase v) Y := by
        rw [not_disjoint_iff] at hd ⊢
        obtain ⟨x, hxW, hxY⟩ := hd
        exact ⟨x, mem_erase.2 ⟨fun h => hvY (h ▸ hxY), hxW⟩, hxY⟩
      have hWp := card_pos.2 ⟨v, hv⟩
      rw [hT _ (by have := card_union_lt this; rw [card_erase_of_mem hv] at this; omega)]
      ring
    rw [← sum_filter_add_sum_filter_not Y (· ∈ W), ← sum_filter_add_sum_filter_not W (· ∈ Y),
      sum_eq_zero (fun v hv => hY v (mem_filter.1 hv).1 (mem_filter.1 hv).2),
      sum_eq_zero (fun v hv => hX v (mem_filter.1 hv).1 (mem_filter.1 hv).2), add_zero, add_zero]
    have hfilt : W.filter (· ∈ Y) = Y.filter (· ∈ W) := by
      ext x; simp only [mem_filter]; tauto
    rw [hfilt, ← sum_add_distrib]
    symm
    refine sum_eq_zero fun v hv => ?_
    obtain ⟨hvY, hvW⟩ := mem_filter.1 hv
    have e : W ∪ Y.erase v = W.erase v ∪ Y := by
      ext x; simp only [mem_union, mem_erase]
      constructor
      · rintro (h | ⟨_, h⟩)
        · by_cases hx : x = v
          · exact Or.inr (hx ▸ hvY)
          · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨_, h⟩ | h)
        · exact Or.inl h
        · by_cases hx : x = v
          · exact Or.inl (hx ▸ hvW)
          · exact Or.inr ⟨hx, h⟩
    rw [e]
    have hsgn : (sg v Y : A) * sgn W (Y.erase v) * sgn U W +
        (-1) ^ (Y.card + (X.filter (v < ·)).card) * (sgn (W.erase v) Y * sgn U (W.erase v)) = 0 := by
      have hWe : W = insert v (W.erase v) := (insert_erase hvW).symm
      have hve : v ∉ W.erase v := notMem_erase v W
      have hYe : Y = insert v (Y.erase v) := (insert_erase hvY).symm
      have hvYe : v ∉ Y.erase v := notMem_erase v Y
      have hvU : v ∉ U := (mem_sdiff.1 hvW).2
      -- inversion counts
      have i1 : inv W (Y.erase v) = inv (W.erase v) (Y.erase v) + ((Y.erase v).filter (· < v)).card := by
        have := inv_insert_left hve (Y.erase v); rwa [← hWe] at this
      have i2 : inv (W.erase v) Y = inv (W.erase v) (Y.erase v) + ((W.erase v).filter (v < ·)).card := by
        have := inv_insert_right (W.erase v) hvYe; rwa [← hYe] at this
      have i3 : inv U W = inv U (W.erase v) + (U.filter (v < ·)).card := by
        have := inv_insert_right U hve; rwa [← hWe] at this
      have i4 : (Y.filter (v < ·)).card = ((Y.erase v).filter (v < ·)).card := by
        congr 1; ext x; simp only [mem_filter, mem_erase]
        exact ⟨fun h => ⟨⟨(ne_of_lt h.2).symm, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
      have i5 := card_lt_add_card_gt hvYe
      have i6 : (Y.erase v).card + 1 = Y.card := card_erase_add_one hvY
      have hXs : X = U ∪ W.erase v ∪ {v} := by
        ext x; simp only [mem_union, mem_singleton, mem_erase, W, mem_sdiff]
        constructor
        · intro hx; by_cases h1 : x ∈ U
          · exact Or.inl (Or.inl h1)
          · by_cases h2 : x = v
            · exact Or.inr h2
            · exact Or.inl (Or.inr ⟨h2, hx, h1⟩)
        · rintro ((h | ⟨_, h, _⟩) | rfl)
          · exact hUX h
          · exact h
          · exact (mem_sdiff.1 hvW).1
      have i7 : (X.filter (v < ·)).card = (U.filter (v < ·)).card + ((W.erase v).filter (v < ·)).card := by
        have d1 : Disjoint U (W.erase v) :=
          disjoint_left.2 fun x hx h => (mem_sdiff.1 (mem_of_mem_erase h)).2 hx
        have d2 : Disjoint (U ∪ W.erase v) {v} := by
          rw [disjoint_singleton_right, mem_union, not_or]; exact ⟨hvU, hve⟩
        conv_lhs => rw [hXs]
        rw [card_filter_union d2, card_filter_union d1]
        simp
      rw [sgn, sgn, sgn, sgn, sg, i1, i2, i3, i4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      refine neg_one_pow_add_eq_zero ?_
      omega
    calc sg v Y * y v * (sgn W (Y.erase v) * sgn U W * S U * T (W.erase v ∪ Y)) +
          (-1) ^ (Y.card + (X.filter (v < ·)).card) * y v *
            (sgn (W.erase v) Y * sgn U (W.erase v) * S U * T (W.erase v ∪ Y))
        = (sg v Y * sgn W (Y.erase v) * sgn U W +
            (-1) ^ (Y.card + (X.filter (v < ·)).card) * (sgn (W.erase v) Y * sgn U (W.erase v))) *
            (y v * S U * T (W.erase v ∪ Y)) := by ring
      _ = 0 := by rw [hsgn, zero_mul]

/-- **Swapping the subset and the leftover element.** -/
theorem sum_powersetCard_sdiff {M : Type*} [AddCommMonoid M] (X : Finset (Fin n)) (p : ℕ)
    (f : Finset (Fin n) → Fin n → M) :
    ∑ U ∈ X.powersetCard p, ∑ a ∈ X \ U, f U a = ∑ a ∈ X, ∑ U ∈ (X.erase a).powersetCard p, f U a := by
  rw [sum_sigma', sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨U, a⟩ hx
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hx ⊢
    exact ⟨hx.2.1, fun b hb => mem_erase.2 ⟨fun h => hx.2.2 (h ▸ hb), hx.1.1 hb⟩, hx.1.2⟩
  · rintro ⟨a, U⟩ hx
    simp only [mem_sigma, mem_powersetCard, mem_sdiff] at hx ⊢
    exact ⟨⟨hx.2.1.trans (erase_subset a X), hx.2.2⟩, hx.1, fun h => notMem_erase a X (hx.2.1 h)⟩
  · rintro ⟨U, a⟩ _; rfl
  · rintro ⟨a, U⟩ _; rfl
  · rintro ⟨U, a⟩ _; rfl

/-- **Subsets of a set with one more element**: those avoiding it and those containing it. -/
theorem sum_powersetCard_insert {M : Type*} [AddCommMonoid M] {a : Fin n} {X : Finset (Fin n)} (ha : a ∉ X)
    (p : ℕ) (g : Finset (Fin n) → M) :
    ∑ U ∈ (insert a X).powersetCard (p + 1), g U =
      ∑ U ∈ X.powersetCard (p + 1), g U + ∑ U ∈ X.powersetCard p, g (insert a U) := by
  rw [powersetCard_succ_insert ha, sum_union, sum_image]
  · intro U hU U' hU' h
    have h1 : a ∉ U := fun h' => ha (mem_powersetCard.1 hU |>.1 h')
    have h2 : a ∉ U' := fun h' => ha (mem_powersetCard.1 hU' |>.1 h')
    rw [← erase_insert h1, ← erase_insert h2]
    exact congrArg (·.erase a) h
  · rw [disjoint_left]
    intro U hU hU'
    obtain ⟨V, -, rfl⟩ := mem_image.1 hU'
    exact ha ((mem_powersetCard.1 hU).1 (mem_insert_self a V))

/-- **(C2) Contracting the right state**: with `|X| + |Y| = p + q` and `T` of degree `q + 1`,
`gar_p(S, y ⌟ T)(X, Y) = Σ_{a ∉ Y} sg(a, Y)·y_a·gar_p(S, T)(X, Y ∪ a)`. -/
theorem gar_contr_right (p : ℕ) {q : ℕ} (y : Fin n → A) (S : Finset (Fin n) → A) {T : Finset (Fin n) → A}
    (hT : IsDeg T (q + 1)) {X Y : Finset (Fin n)} (hXY : X.card + Y.card = p + q) :
    gar p S (contr y T) X Y = ∑ a ∈ Yᶜ, sg a Y * y a * gar p S T X (insert a Y) := by
  simp only [gar, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun U hU => ?_
  rw [mem_powersetCard] at hU
  obtain ⟨hUX, hUc⟩ := hU
  have hW : (X \ U).card + Y.card = q := by
    have := card_sdiff_add hUX
    omega
  set W := X \ U with hWdef
  by_cases hd : Disjoint W Y
  · rw [contr, mul_sum]
    have hsplit : Yᶜ = (W ∪ Y)ᶜ ∪ W := by
      ext x; simp only [mem_compl, mem_union]; constructor
      · intro hx; by_cases h : x ∈ W
        · exact Or.inr h
        · exact Or.inl (by simp [h, hx])
      · rintro (h | h)
        · exact fun hY => h (Or.inr hY)
        · exact fun hY => disjoint_left.1 hd h hY
    rw [hsplit, sum_union (disjoint_left.2 fun x h1 h2 => (mem_compl.1 h1) (mem_union_left _ h2))]
    rw [sum_eq_zero (s := W) fun a ha => by
      rw [union_insert, insert_eq_of_mem (mem_union_left _ ha),
        hT _ (by rw [card_union_of_disjoint hd]; omega)]
      ring, add_zero]
    refine sum_congr rfl fun a ha => ?_
    have haW : a ∉ W := fun h => mem_compl.1 ha (mem_union_left _ h)
    have haY : a ∉ Y := fun h => mem_compl.1 ha (mem_union_right _ h)
    have e : insert a (W ∪ Y) = W ∪ insert a Y := by rw [union_insert]
    rw [e]
    have hsgn : (sgn W Y : A) * sg a (W ∪ Y) = sg a Y * sgn W (insert a Y) := by
      rw [sgn, sgn, sg, sg, inv_insert_right W haY, card_filter_union hd, ← pow_add, ← pow_add]
      refine neg_one_pow_congr ?_
      omega
    calc sgn W Y * sgn U W * S U * (sg a (W ∪ Y) * y a * T (W ∪ insert a Y))
        = (sgn W Y * sg a (W ∪ Y)) * sgn U W * y a * S U * T (W ∪ insert a Y) := by ring
      _ = _ := by rw [hsgn]; ring
  · have hu := card_union_lt hd
    rw [((hT.contr y) _ (by omega)), mul_zero]
    refine (sum_eq_zero fun a _ => ?_).symm
    have : (W ∪ insert a Y).card ≠ q + 1 := by
      have h1 : (W ∪ insert a Y).card ≤ (W ∪ Y).card + 1 := by
        rw [union_insert]; exact card_insert_le _ _
      omega
    rw [hT _ this]
    ring

/-- **A set is a subset and its complement in a superset.** -/
theorem insert_sdiff_insert_of_notMem {a : Fin n} {X U : Finset (Fin n)} (ha : a ∉ X) :
    insert a X \ insert a U = X \ U := by
  ext x; simp only [mem_sdiff, mem_insert]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact ⟨h1, fun h => h2 (Or.inr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr h1, fun h => h.elim (fun h' => ha (h' ▸ h1)) h2⟩

/-- **(C1) Contracting the left state**: with `|X| + |Y| = p + q` and `T` of degree `q`,
`gar_p(y ⌟ S, T)(X, Y) = Σ_{a ∉ X} ±y_a·gar_{p+1}(S, T)(X ∪ a, Y) − Σ_{a ∉ Y} ±y_a·gar_{p+1}(S, T)(X, Y ∪ a)`, the
signs being `(−1)^{p + #{x ∈ X : x < a}}` and `(−1)^{p + |X| + #{z ∈ Y : z < a}}`. -/
theorem gar_contr_left (p : ℕ) {q : ℕ} (y : Fin n → A) (S : Finset (Fin n) → A) {T : Finset (Fin n) → A}
    (hT : IsDeg T q) {X Y : Finset (Fin n)} (hXY : X.card + Y.card = p + q) :
    gar p (contr y S) T X Y =
      ∑ a ∈ Xᶜ, (-1) ^ (p + (X.filter (· < a)).card) * y a * gar (p + 1) S T (insert a X) Y -
        ∑ a ∈ Yᶜ, (-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a * gar (p + 1) S T X (insert a Y) := by
  set L : Finset (Fin n) → Fin n → A := fun U a =>
    sgn (X \ U) Y * sgn U (X \ U) * (sg a U * y a * S (insert a U)) * T ((X \ U) ∪ Y) with hL
  have hlhs : gar p (contr y S) T X Y =
      ∑ U ∈ X.powersetCard p, ∑ a ∈ Xᶜ, L U a + ∑ U ∈ X.powersetCard p, ∑ a ∈ X \ U, L U a := by
    rw [← sum_add_distrib, gar]
    refine sum_congr rfl fun U hU => ?_
    have hUX := (mem_powersetCard.1 hU).1
    have hc : Uᶜ = Xᶜ ∪ X \ U := by
      ext x; simp only [mem_compl, mem_union, mem_sdiff]
      constructor
      · intro h; by_cases hx : x ∈ X
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl hx
      · rintro (h | ⟨_, h⟩)
        · exact fun hx => h (hUX hx)
        · exact h
    have hd : Disjoint Xᶜ (X \ U) := disjoint_left.2 fun x h1 h2 => mem_compl.1 h1 (mem_sdiff.1 h2).1
    rw [← sum_union hd, ← hc, contr, mul_sum, sum_mul]
  -- the first part is the `a ∈ U`-half of the first sum
  have hfirst : ∑ U ∈ X.powersetCard p, ∑ a ∈ Xᶜ, L U a =
      ∑ a ∈ Xᶜ, (-1) ^ (p + (X.filter (· < a)).card) * y a * ∑ U ∈ X.powersetCard p,
        (sgn (insert a X \ insert a U) Y * sgn (insert a U) (insert a X \ insert a U) * S (insert a U) *
          T ((insert a X \ insert a U) ∪ Y)) := by
    rw [sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [mul_sum]
    refine sum_congr rfl fun U hU => ?_
    have haX : a ∉ X := mem_compl.1 ha
    obtain ⟨hUX, hUc⟩ := mem_powersetCard.1 hU
    have haU : a ∉ U := fun h => haX (hUX h)
    rw [insert_sdiff_insert_of_notMem haX]
    have hsgn : (sgn U (X \ U) : A) * sg a U =
        (-1) ^ (p + (X.filter (· < a)).card) * sgn (insert a U) (X \ U) := by
      rw [sgn, sgn, sg, inv_insert_left haU, ← pow_add, ← pow_add]
      refine neg_one_pow_congr ?_
      have h1 := card_lt_add_card_gt haU
      have h2 : (X.filter (· < a)).card = (U.filter (· < a)).card + ((X \ U).filter (· < a)).card := by
        conv_lhs => rw [← union_sdiff_of_subset hUX]
        exact card_filter_union disjoint_sdiff _
      omega
    simp only [hL]
    calc sgn (X \ U) Y * sgn U (X \ U) * (sg a U * y a * S (insert a U)) * T ((X \ U) ∪ Y)
        = sgn (X \ U) Y * (sgn U (X \ U) * sg a U) * y a * S (insert a U) * T ((X \ U) ∪ Y) := by ring
      _ = _ := by rw [hsgn]; ring
  -- the second part cancels the `a ∈ X`-half of the second sum
  have hsecond : ∑ U ∈ X.powersetCard p, ∑ a ∈ X \ U, L U a =
      -∑ a ∈ Yᶜ.filter (· ∈ X), (-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a *
        ∑ U ∈ (X.erase a).powersetCard p, (sgn (X \ insert a U) (insert a Y) *
          sgn (insert a U) (X \ insert a U) * S (insert a U) * T ((X \ insert a U) ∪ insert a Y)) := by
    rw [sum_powersetCard_sdiff, ← sum_filter_add_sum_filter_not X (· ∈ Y)]
    rw [sum_eq_zero (s := X.filter (· ∈ Y)) fun a ha => sum_eq_zero fun U hU => by
      obtain ⟨haX, haY⟩ := mem_filter.1 ha
      obtain ⟨hUX, hUc⟩ := mem_powersetCard.1 hU
      have haU : a ∉ U := fun h => notMem_erase a X (hUX h)
      have hUX' : U ⊆ X := hUX.trans (erase_subset a X)
      have hnd : ¬ Disjoint (X \ U) Y := not_disjoint_iff.2 ⟨a, mem_sdiff.2 ⟨haX, haU⟩, haY⟩
      have := card_union_lt hnd
      have := card_sdiff_add hUX'
      simp only [hL]
      rw [hT _ (by omega), mul_zero], zero_add]
    have hf : X.filter (· ∉ Y) = Yᶜ.filter (· ∈ X) := by
      ext x; simp only [mem_filter, mem_compl]; tauto
    rw [hf, ← sum_neg_distrib]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haY, haX⟩ := mem_filter.1 ha
    have haY' : a ∉ Y := mem_compl.1 haY
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun U hU => ?_
    obtain ⟨hUX, hUc⟩ := mem_powersetCard.1 hU
    have haU : a ∉ U := fun h => notMem_erase a X (hUX h)
    have hUX' : U ⊆ X := hUX.trans (erase_subset a X)
    have haW : a ∈ X \ U := mem_sdiff.2 ⟨haX, haU⟩
    have e1 : X \ insert a U = (X \ U).erase a := by
      ext x; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    have e2 : (X \ U).erase a ∪ insert a Y = (X \ U) ∪ Y := by
      rw [union_insert, ← insert_union, insert_erase haW]
    rw [e1, e2]
    have i7 := card_sdiff_add hUX'
    set W := X \ U
    have hWe : insert a (W.erase a) = W := insert_erase haW
    have hve : a ∉ W.erase a := notMem_erase a W
    have hsgn : (sgn W Y : A) * sgn U W * sg a U +
        (-1) ^ (p + X.card + (Y.filter (· < a)).card) *
          (sgn (W.erase a) (insert a Y) * sgn (insert a U) (W.erase a)) = 0 := by
      have i1 : inv W Y = inv (W.erase a) Y + (Y.filter (· < a)).card := by
        have := inv_insert_left hve Y; rwa [hWe] at this
      have i2 : inv U W = inv U (W.erase a) + (U.filter (a < ·)).card := by
        have := inv_insert_right U hve; rwa [hWe] at this
      have i3 := inv_insert_right (W.erase a) haY'
      have i4 := inv_insert_left haU (W.erase a)
      have i5 := card_lt_add_card_gt hve
      have i6 : (W.erase a).card + 1 = W.card := card_erase_add_one haW
      rw [sgn, sgn, sgn, sgn, sg, i1, i2, i3, i4, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      refine neg_one_pow_add_eq_zero ?_
      omega
    simp only [hL]
    calc sgn W Y * sgn U W * (sg a U * y a * S (insert a U)) * T (W ∪ Y)
        = (sgn W Y * sgn U W * sg a U) * (y a * S (insert a U) * T (W ∪ Y)) := by ring
      _ = -((-1) ^ (p + X.card + (Y.filter (· < a)).card) *
          (sgn (W.erase a) (insert a Y) * sgn (insert a U) (W.erase a))) *
            (y a * S (insert a U) * T (W ∪ Y)) := by rw [eq_neg_of_add_eq_zero_left hsgn]
      _ = _ := by ring
  -- the first sum splits by `a ∈ U''`
  have hR1 : ∑ a ∈ Xᶜ, (-1) ^ (p + (X.filter (· < a)).card) * y a * gar (p + 1) S T (insert a X) Y =
      ∑ a ∈ Xᶜ, (-1) ^ (p + (X.filter (· < a)).card) * y a * ∑ U ∈ X.powersetCard (p + 1),
        (sgn (insert a X \ U) Y * sgn U (insert a X \ U) * S U * T ((insert a X \ U) ∪ Y)) +
      ∑ a ∈ Xᶜ, (-1) ^ (p + (X.filter (· < a)).card) * y a * ∑ U ∈ X.powersetCard p,
        (sgn (insert a X \ insert a U) Y * sgn (insert a U) (insert a X \ insert a U) * S (insert a U) *
          T ((insert a X \ insert a U) ∪ Y)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a ha => ?_
    rw [gar, sum_powersetCard_insert (mem_compl.1 ha), mul_add]
  -- the second sum splits by `a ∈ X`
  have hR2 : ∑ a ∈ Yᶜ, (-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a * gar (p + 1) S T X (insert a Y) =
      ∑ a ∈ Yᶜ.filter (· ∈ X), (-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a *
        ∑ U ∈ (X.erase a).powersetCard p, (sgn (X \ insert a U) (insert a Y) *
          sgn (insert a U) (X \ insert a U) * S (insert a U) * T ((X \ insert a U) ∪ insert a Y)) +
      ∑ a ∈ Yᶜ.filter (· ∉ X), (-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a *
        gar (p + 1) S T X (insert a Y) := by
    rw [← sum_filter_add_sum_filter_not Yᶜ (· ∈ X)]
    congr 1
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haY, haX⟩ := mem_filter.1 ha
    have haY' : a ∉ Y := mem_compl.1 haY
    congr 1
    have hX : X = insert a (X.erase a) := (insert_erase haX).symm
    rw [gar]
    conv_lhs => rw [hX]
    rw [sum_powersetCard_insert (notMem_erase a X), ← hX]
    rw [sum_eq_zero (s := (X.erase a).powersetCard (p + 1)) fun U hU => by
      obtain ⟨hUX, hUc⟩ := mem_powersetCard.1 hU
      have haU : a ∉ U := fun h => notMem_erase a X (hUX h)
      have hUX' : U ⊆ X := hUX.trans (erase_subset a X)
      have haW : a ∈ X \ U := mem_sdiff.2 ⟨haX, haU⟩
      have e : (X \ U) ∪ insert a Y = (X \ U) ∪ Y := by rw [union_insert, insert_eq_of_mem (mem_union_left _ haW)]
      have h1 := card_sdiff_add hUX'
      have h2 := card_union_le (X \ U) Y
      rw [e, hT _ (by omega), mul_zero], zero_add]
  -- the leftover parts agree
  have hE : ∑ a ∈ Xᶜ, (-1) ^ (p + (X.filter (· < a)).card) * y a * ∑ U ∈ X.powersetCard (p + 1),
        (sgn (insert a X \ U) Y * sgn U (insert a X \ U) * S U * T ((insert a X \ U) ∪ Y)) =
      ∑ a ∈ Yᶜ.filter (· ∉ X), (-1) ^ (p + X.card + (Y.filter (· < a)).card) * y a *
        gar (p + 1) S T X (insert a Y) := by
    rw [← sum_filter_add_sum_filter_not Xᶜ (· ∈ Y)]
    rw [sum_eq_zero (s := Xᶜ.filter (· ∈ Y)) fun a ha => by
      obtain ⟨haX, haY⟩ := mem_filter.1 ha
      have haX' : a ∉ X := mem_compl.1 haX
      rw [sum_eq_zero fun U hU => ?_, mul_zero]
      obtain ⟨hUX, hUc⟩ := mem_powersetCard.1 hU
      have haU : a ∉ U := fun h => haX' (hUX h)
      have e1 : insert a X \ U = insert a (X \ U) := by
        ext x; simp only [mem_sdiff, mem_insert]
        constructor
        · rintro ⟨h | h, hU⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hU⟩
        · rintro (h | ⟨h, hU⟩)
          · exact ⟨Or.inl h, h ▸ haU⟩
          · exact ⟨Or.inr h, hU⟩
      have e2 : insert a (X \ U) ∪ Y = (X \ U) ∪ Y := by
        rw [insert_union, insert_eq_of_mem (mem_union_right _ haY)]
      have h1 := card_sdiff_add hUX
      have h2 := card_union_le (X \ U) Y
      rw [e1, e2, hT _ (by omega), mul_zero], zero_add]
    have hf : Xᶜ.filter (· ∉ Y) = Yᶜ.filter (· ∉ X) := by
      ext x; simp only [mem_filter, mem_compl]; tauto
    rw [hf]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨haY, haX⟩ := mem_filter.1 ha
    have haY' : a ∉ Y := mem_compl.1 haY
    rw [gar, mul_sum, mul_sum]
    refine sum_congr rfl fun U hU => ?_
    obtain ⟨hUX, hUc⟩ := mem_powersetCard.1 hU
    have haU : a ∉ U := fun h => haX (hUX h)
    have haW : a ∉ X \ U := fun h => haX (mem_sdiff.1 h).1
    have e1 : insert a X \ U = insert a (X \ U) := by
      ext x; simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨h | h, hU⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, hU⟩
      · rintro (h | ⟨h, hU⟩)
        · exact ⟨Or.inl h, h ▸ haU⟩
        · exact ⟨Or.inr h, hU⟩
    have e2 : insert a (X \ U) ∪ Y = (X \ U) ∪ insert a Y := by rw [insert_union, union_insert]
    rw [e1, e2]
    have h1 := card_sdiff_add hUX
    have hsgn : (-1 : A) ^ (p + (X.filter (· < a)).card) * (sgn (insert a (X \ U)) Y * sgn U (insert a (X \ U))) =
        (-1) ^ (p + X.card + (Y.filter (· < a)).card) * (sgn (X \ U) (insert a Y) * sgn U (X \ U)) := by
      rw [sgn, sgn, sgn, sgn, inv_insert_left haW, inv_insert_right U haW, inv_insert_right (X \ U) haY',
        ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      refine neg_one_pow_congr ?_
      have i1 := card_lt_add_card_gt haX
      have i2 : (X.filter (a < ·)).card = (U.filter (a < ·)).card + ((X \ U).filter (a < ·)).card := by
        conv_lhs => rw [← union_sdiff_of_subset hUX]
        exact card_filter_union disjoint_sdiff _
      omega
    calc (-1) ^ (p + (X.filter (· < a)).card) * y a *
          (sgn (insert a (X \ U)) Y * sgn U (insert a (X \ U)) * S U * T ((X \ U) ∪ insert a Y))
        = ((-1) ^ (p + (X.filter (· < a)).card) * (sgn (insert a (X \ U)) Y * sgn U (insert a (X \ U)))) *
          (y a * S U * T ((X \ U) ∪ insert a Y)) := by ring
      _ = _ := by rw [hsgn]; ring
  rw [hlhs, hfirst, hsecond, hR1, hR2, hE]
  ring

end Gar

/-! ## Column paths: Pieri paths by their column heights -/

section HPath

variable {n : ℕ}

/-- **The initial column heights**: `n` for `c ≤ 0`, `0` for `c ≥ 1`. -/
def h0 (n : ℕ) (c : ℤ) : ℕ := if c ≤ 0 then n else 0

/-- **The column window** `[−T, T]`. -/
abbrev win (T : ℕ) : Finset ℤ := Icc (-(T : ℤ)) T

/-- **A column path** of type `(vec, B)` with `N` letters in `n` coordinates and window `T`: column heights
`h t c` after `t` letters, antitone in `c`, at most `n`, starting at `h0`, constant outside `(−T, T)`; a vector
letter raises `B_t` heights by one, a covector letter lowers `B_t` heights by one. These are the Pieri paths of
`PathBasis` read through their column heights (`HPath.toPieri`). -/
structure HPath (n N T : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ) where
  /-- **The heights**: `h t c` after `t` letters. -/
  h : ℕ → ℤ → ℕ
  zero : ∀ c, h 0 c = h0 n c
  anti : ∀ t ≤ N, Antitone (h t)
  le : ∀ t ≤ N, ∀ c, h t c ≤ n
  out : ∀ t ≤ N, ∀ c, c ∉ Ioo (-(T : ℤ)) T → h t c = h0 n c
  up : ∀ t < N, vec t = true → ∀ c, h t c ≤ h (t + 1) c ∧ h (t + 1) c ≤ h t c + 1
  down : ∀ t < N, vec t = false → ∀ c, h (t + 1) c ≤ h t c ∧ h t c ≤ h (t + 1) c + 1
  card : ∀ t < N, ((win T).filter fun c => h t c ≠ h (t + 1) c).card = B t

variable {N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The columns changed by the letter `t`.** -/
def HPath.chg (P : HPath n N T vec B) (t : ℕ) : Finset ℤ := (win T).filter fun c => P.h t c ≠ P.h (t + 1) c

/-- **Forgetting the last letter.** -/
def HPath.trunc (P : HPath n (N + 1) T vec B) : HPath n N T vec B where
  h := P.h
  zero := P.zero
  anti t ht := P.anti t (by omega)
  le t ht := P.le t (by omega)
  out t ht := P.out t (by omega)
  up t ht := P.up t (by omega)
  down t ht := P.down t (by omega)
  card t ht := P.card t (by omega)

/-- **The step of the column `c` at the letter `t`** (column coordinates): wedge if its height grows, contract if
it drops, keep otherwise. -/
def ustep (h : ℕ → ℤ → ℕ) (c : ℤ) (t : ℕ) : Step :=
  if h t c < h (t + 1) c then .wed else if h (t + 1) c < h t c then .con else .keep

/-- **The initial state** of the column `c` (column coordinates): `[|J| = h0(c)]`, i.e. `[J = univ]` for `c ≤ 0`
and `[J = ∅]` for `c ≥ 1`. -/
def ust0 (n : ℕ) (c : ℤ) : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ := fun J => if J.card = h0 n c then 1 else 0

/-- **The state after `t` letters** from an initial state `S0`, for steps `st`. -/
def ust (st : ℕ → Step) (S0 : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) :
    ℕ → Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ
  | 0 => S0
  | t + 1 => (st t).app (fun a => X (t, a)) (ust st S0 t)

/-- **The column state** of the column `c` of a height function after `t` letters. -/
def colS (h : ℕ → ℤ → ℕ) (c : ℤ) (t : ℕ) : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ :=
  ust (ustep h c) (ust0 n c) t

/-- **The path polynomial in column coordinates**: `Ψ(P, C) = ∏_{c ∈ [−T, T]} S_c(C(c))`. -/
def psi (P : HPath n N T vec B) (C : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) ℤ :=
  ∏ c ∈ win T, colS P.h c N (C c)

/-- **The step of a letter of type `v`** applied to a state. -/
def lstep (v : Bool) (t : ℕ) (S : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) :
    Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ :=
  if v then wedge (fun a => X (t, a)) S else contr (fun a => X (t, a)) S

/-- **A configuration**: the states of `R` after `N` letters, the columns of `D` stepped once more by the letter `N`. -/
def conf (R : HPath n N T vec B) (D : Finset ℤ) (C : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) ℤ :=
  ∏ c ∈ win T, (if c ∈ D then lstep (vec N) N (colS R.h c N) else colS R.h c N) (C c)

/-- **The column states after one more letter.** -/
theorem colS_succ (h : ℕ → ℤ → ℕ) (c : ℤ) (t : ℕ) :
    (colS h c (t + 1) : Finset (Fin n) → _) = (ustep h c t).app (fun a => X (t, a)) (colS h c t) := rfl

/-- **The path polynomial is the configuration of its truncation and its last letter.** -/
theorem psi_eq_conf (P : HPath n (N + 1) T vec B) (C : ℤ → Finset (Fin n)) :
    psi P C = conf P.trunc (P.chg N) C := by
  refine prod_congr rfl fun c hc => ?_
  rw [colS_succ]
  have hst : ustep P.h c N = if c ∈ P.chg N then (if vec N then Step.wed else Step.con) else Step.keep := by
    unfold ustep HPath.chg
    simp only [mem_filter, hc, true_and]
    have hu := P.up N (by omega)
    have hd := P.down N (by omega)
    cases hv : vec N
    · have := hd hv c
      by_cases h1 : P.h N c < P.h (N + 1) c
      · omega
      · by_cases h2 : P.h (N + 1) c < P.h N c
        · simp [h1, h2, show P.h N c ≠ P.h (N + 1) c by omega]
        · simp [show P.h N c = P.h (N + 1) c by omega]
    · have := hu hv c
      by_cases h1 : P.h N c < P.h (N + 1) c
      · simp [h1, show P.h N c ≠ P.h (N + 1) c by omega]
      · by_cases h2 : P.h (N + 1) c < P.h N c
        · omega
        · simp [show P.h N c = P.h (N + 1) c by omega]
  rw [hst]
  simp only [HPath.trunc, lstep]
  split_ifs <;> rfl

end HPath

/-! ## Degrees of the column states, the order on paths and the lower part -/

section Order

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The column states depend only on the heights so far.** -/
theorem colS_congr {h h' : ℕ → ℤ → ℕ} (c : ℤ) {t : ℕ} (hh : ∀ s ≤ t, h s = h' s) :
    (colS h c t : Finset (Fin n) → _) = colS h' c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [colS_succ, colS_succ, ih fun s hs => hh s (by omega)]
    unfold ustep
    rw [hh t (by omega), hh (t + 1) le_rfl]

/-- **The column states have the degree of their heights.** -/
theorem HPath.isDeg (P : HPath n N T vec B) (c : ℤ) {t : ℕ} (ht : t ≤ N) :
    IsDeg (colS (n := n) P.h c t) (P.h t c) := by
  induction t with
  | zero =>
    intro J hJ
    rw [P.zero] at hJ
    simp [colS, ust, ust0, hJ]
  | succ t ih =>
    have ih := ih (by omega)
    rw [colS_succ]
    unfold ustep
    have hs : (vec t = true → P.h t c ≤ P.h (t + 1) c ∧ P.h (t + 1) c ≤ P.h t c + 1) ∧
        (vec t = false → P.h (t + 1) c ≤ P.h t c ∧ P.h t c ≤ P.h (t + 1) c + 1) :=
      ⟨fun hv => P.up t (by omega) hv c, fun hv => P.down t (by omega) hv c⟩
    split_ifs with h1 h2
    · have e : P.h (t + 1) c = P.h t c + 1 := by cases hv : vec t <;> simp_all <;> omega
      rw [e]
      exact ih.wedge _
    · have e : P.h t c = P.h (t + 1) c + 1 := by cases hv : vec t <;> simp_all <;> omega
      rw [e] at ih
      exact ih.contr _
    · have e : P.h (t + 1) c = P.h t c := by omega
      rw [e]
      exact ih

/-- **The weight of a column of height `k`**: `Σ_{i < k} (n − i)`. -/
def wt (n k : ℕ) : ℕ := ∑ i ∈ range k, (n - i)

/-- **The potential of the heights after `t` letters**: `Σ_c wt(h_t(c))`; it orders the paths. -/
def phi (P : HPath n N T vec B) (t : ℕ) : ℕ := ∑ c ∈ win T, wt n (P.h t c)

/-- **The order on paths**: lexicographic in the potentials after `1, …, N` letters. -/
def HPath.lt (Q P : HPath n N T vec B) : Prop :=
  ∃ t ≤ N, (∀ s < t, phi Q s = phi P s) ∧ phi Q t < phi P t

/-- **The potentials as a lexicographic vector.** -/
def phiLex (P : HPath n N T vec B) : Lex (Fin (N + 1) → ℕ) := toLex fun t => phi P t

/-- **The order is the lexicographic order of the potentials.** -/
theorem HPath.lt_phiLex {Q P : HPath n N T vec B} (h : Q.lt P) : phiLex Q < phiLex P := by
  obtain ⟨t, ht, h1, h2⟩ := h
  exact ⟨⟨t, by omega⟩, fun j hj => h1 j hj, h2⟩

/-- **The order on paths is well founded.** -/
theorem HPath.lt_wf : WellFounded (HPath.lt : HPath n N T vec B → HPath n N T vec B → Prop) :=
  Subrelation.wf (fun h => HPath.lt_phiLex h) (InvImage.wf phiLex wellFounded_lt)

/-- **The lower part** `F_{≺P}`: the `ℤ`-span of the path polynomials `Ψ(Q, C)` of the paths `Q ≺ P`, for all fillings
`C` (standard or not). -/
def lower (P : HPath n N T vec B) : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ) :=
  Submodule.span ℤ {f | ∃ Q : HPath n N T vec B, Q.lt P ∧ ∃ C, f = psi Q C}

/-- **The path polynomials of lower paths lie in the lower part.** -/
theorem psi_mem_lower {Q P : HPath n N T vec B} (h : Q.lt P) (C : ℤ → Finset (Fin n)) : psi Q C ∈ lower P :=
  Submodule.subset_span ⟨Q, h, C, rfl⟩

end Order

/-! ## Extending a path by a strip in the first or the last row -/

section Ext

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **A column whose height moved was changed by some letter.** -/
theorem HPath.exists_chg (P : HPath n N T vec B) {c : ℤ} (hc : c ∈ win T) (h : P.h N c ≠ h0 n c) :
    ∃ s < N, c ∈ P.chg s := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have : ∀ t ≤ N, P.h t c = h0 n c := by
    intro t ht
    induction t with
    | zero => exact P.zero c
    | succ t ih =>
      have := hne t (by omega)
      simp only [HPath.chg, mem_filter, hc, true_and, not_not] at this
      rw [← this, ih (by omega)]
  exact h (this N le_rfl)

/-- **At most `Σ_{s < N} B_s` columns have moved.** -/
theorem HPath.card_moved (P : HPath n N T vec B) :
    ((win T).filter fun c => P.h N c ≠ h0 n c).card ≤ ∑ s ∈ range N, B s := by
  calc ((win T).filter fun c => P.h N c ≠ h0 n c).card ≤ ((range N).biUnion P.chg).card := by
        refine card_le_card fun c hc => ?_
        obtain ⟨hcw, hch⟩ := mem_filter.1 hc
        obtain ⟨s, hs, hcs⟩ := P.exists_chg hcw hch
        exact mem_biUnion.2 ⟨s, mem_range.2 hs, hcs⟩
    _ ≤ ∑ s ∈ range N, (P.chg s).card := card_biUnion_le
    _ = ∑ s ∈ range N, B s := sum_congr rfl fun s hs => P.card s (mem_range.1 hs)

/-- **The left end of the window is full.** -/
theorem HPath.h_neg (P : HPath n N T vec B) {t : ℕ} (ht : t ≤ N) : P.h t (-(T : ℤ)) = n := by
  rw [P.out t ht _ (by simp), h0, ite_eq_left (by omega)]

/-- **The last column of positive height** after `N` letters. -/
def HPath.top (P : HPath n N T vec B) (hn : 0 < n) : ℤ :=
  ((win T).filter fun c => 1 ≤ P.h N c).max' ⟨-(T : ℤ), mem_filter.2 ⟨by simp, by rw [P.h_neg le_rfl]; omega⟩⟩

/-- **The last column of full height** after `N` letters. -/
def HPath.bot (P : HPath n N T vec B) : ℤ :=
  ((win T).filter fun c => P.h N c = n).max' ⟨-(T : ℤ), mem_filter.2 ⟨by simp, P.h_neg le_rfl⟩⟩

/-- **The columns up to the top have positive height, the later ones height zero.** -/
theorem HPath.top_spec (P : HPath n N T vec B) (hn : 0 < n) :
    -(T : ℤ) ≤ P.top hn ∧ P.top hn ≤ T ∧ (∀ c ≤ P.top hn, 1 ≤ P.h N c) ∧ ∀ c, P.top hn < c → P.h N c = 0 := by
  have hm : P.top hn ∈ (win T).filter fun c => 1 ≤ P.h N c := max'_mem _ _
  rw [mem_filter, mem_Icc] at hm
  refine ⟨hm.1.1, hm.1.2, fun c hc => le_trans hm.2 (P.anti N le_rfl hc), fun c hc => ?_⟩
  by_cases hcT : c ≤ T
  · by_contra h0'
    have hmem : c ∈ (win T).filter fun c => 1 ≤ P.h N c :=
      mem_filter.2 ⟨mem_Icc.2 ⟨by have := hm.1.1; omega, hcT⟩, by omega⟩
    exact absurd (le_max' _ c hmem : c ≤ P.top hn) (not_le.2 hc)
  · rw [P.out N le_rfl c (by simp; omega), h0, ite_eq_right (by omega)]

/-- **The columns up to the bottom are full, the later ones are not.** -/
theorem HPath.bot_spec (P : HPath n N T vec B) (hn : 0 < n) :
    -(T : ℤ) ≤ P.bot ∧ P.bot ≤ T ∧ (∀ c ≤ P.bot, P.h N c = n) ∧ ∀ c, P.bot < c → P.h N c < n := by
  have hm : P.bot ∈ (win T).filter fun c => P.h N c = n := max'_mem _ _
  rw [mem_filter, mem_Icc] at hm
  refine ⟨hm.1.1, hm.1.2, fun c hc => le_antisymm (P.le N le_rfl c) (by have := P.anti N le_rfl hc; omega),
    fun c hc => ?_⟩
  have hle := P.le N le_rfl c
  by_cases hcT : c ≤ T
  · by_contra h0'
    have hmem : c ∈ (win T).filter fun c => P.h N c = n :=
      mem_filter.2 ⟨mem_Icc.2 ⟨by have := hm.1.1; omega, hcT⟩, by omega⟩
    exact absurd (le_max' _ c hmem : c ≤ P.bot) (not_le.2 hc)
  · rw [P.out N le_rfl c (by simp; omega), h0, ite_eq_right (by omega)]
    exact hn

/-- **The top is at most the number of moves.** -/
theorem HPath.top_le (P : HPath n N T vec B) (hn : 0 < n) : P.top hn ≤ ((∑ s ∈ range N, B s : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3, -⟩ := P.top_spec hn
  have hsub : Icc 1 (P.top hn) ⊆ (win T).filter fun c => P.h N c ≠ h0 n c := fun c hc => by
    rw [mem_Icc] at hc
    refine mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [h0, ite_eq_right (by omega)]
    have := h3 c hc.2
    omega
  have := (card_le_card hsub).trans P.card_moved
  rw [Int.card_Icc] at this
  omega

/-- **The bottom is at least minus the number of moves.** -/
theorem HPath.bot_ge (P : HPath n N T vec B) (hn : 0 < n) : -P.bot ≤ ((∑ s ∈ range N, B s : ℕ) : ℤ) := by
  obtain ⟨h1, h2, -, h4⟩ := P.bot_spec hn
  have hsub : Ioc P.bot 0 ⊆ (win T).filter fun c => P.h N c ≠ h0 n c := fun c hc => by
    rw [mem_Ioc] at hc
    refine mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [h0, ite_eq_left hc.2]
    exact (h4 c hc.1).ne
  have := (card_le_card hsub).trans P.card_moved
  rw [Int.card_Ioc] at this
  omega


/-- **Appending a letter** to a path: the heights `h'` after it. -/
def HPath.snoc (P : HPath n N T vec B) (h' : ℤ → ℕ) (hanti : Antitone h') (hle : ∀ c, h' c ≤ n)
    (hout : ∀ c, c ∉ Ioo (-(T : ℤ)) T → h' c = h0 n c)
    (hup : vec N = true → ∀ c, P.h N c ≤ h' c ∧ h' c ≤ P.h N c + 1)
    (hdown : vec N = false → ∀ c, h' c ≤ P.h N c ∧ P.h N c ≤ h' c + 1)
    (hcard : ((win T).filter fun c => P.h N c ≠ h' c).card = B N) : HPath n (N + 1) T vec B where
  h t c := if t ≤ N then P.h t c else h' c
  zero c := by simp [P.zero]
  anti t ht := by
    by_cases h : t ≤ N
    · simp only [h, ↓reduceIte]; exact P.anti t h
    · simp only [h, ↓reduceIte]; exact hanti
  le t ht c := by
    by_cases h : t ≤ N
    · simp only [h, ↓reduceIte]; exact P.le t h c
    · simp only [h, ↓reduceIte]; exact hle c
  out t ht c hc := by
    by_cases h : t ≤ N
    · simp only [h, ↓reduceIte]; exact P.out t h c hc
    · simp only [h, ↓reduceIte]; exact hout c hc
  up t ht hv c := by
    by_cases h : t + 1 ≤ N
    · simp only [h, show t ≤ N by omega, ↓reduceIte]; exact P.up t (by omega) hv c
    · have e : t = N := by omega
      subst e
      simp only [le_rfl, ↓reduceIte, show ¬ t + 1 ≤ t by omega]; exact hup hv c
  down t ht hv c := by
    by_cases h : t + 1 ≤ N
    · simp only [h, show t ≤ N by omega, ↓reduceIte]; exact P.down t (by omega) hv c
    · have e : t = N := by omega
      subst e
      simp only [le_rfl, ↓reduceIte, show ¬ t + 1 ≤ t by omega]; exact hdown hv c
  card t ht := by
    by_cases h : t + 1 ≤ N
    · simp only [h, show t ≤ N by omega, ↓reduceIte]; exact P.card t (by omega)
    · have e : t = N := by omega
      subst e
      simp only [le_rfl, ↓reduceIte, show ¬ t + 1 ≤ t by omega]; exact hcard

section Snoc

variable (P : HPath n N T vec B) (h' : ℤ → ℕ) (hanti : Antitone h') (hle : ∀ c, h' c ≤ n)
  (hout : ∀ c, c ∉ Ioo (-(T : ℤ)) T → h' c = h0 n c)
  (hup : vec N = true → ∀ c, P.h N c ≤ h' c ∧ h' c ≤ P.h N c + 1)
  (hdown : vec N = false → ∀ c, h' c ≤ P.h N c ∧ P.h N c ≤ h' c + 1)
  (hcard : ((win T).filter fun c => P.h N c ≠ h' c).card = B N)

/-- **The heights of an appended path** up to `N` are those of the path. -/
theorem HPath.snoc_h_le {t : ℕ} (ht : t ≤ N) : (P.snoc h' hanti hle hout hup hdown hcard).h t = P.h t := by
  funext c; simp [HPath.snoc, ht]

/-- **The heights of an appended path** after the new letter. -/
theorem HPath.snoc_h_succ : (P.snoc h' hanti hle hout hup hdown hcard).h (N + 1) = h' := by
  funext c; simp [HPath.snoc]

/-- **The path polynomial of an appended path** is a configuration of the path. -/
theorem HPath.psi_snoc (C : ℤ → Finset (Fin n)) :
    psi (P.snoc h' hanti hle hout hup hdown hcard) C = conf P ((win T).filter fun c => P.h N c ≠ h' c) C := by
  rw [psi_eq_conf]
  unfold conf HPath.chg
  have e1 : ∀ c, (colS (P.snoc h' hanti hle hout hup hdown hcard).trunc.h c N : Finset (Fin n) → _) = colS P.h c N :=
    fun c => colS_congr c fun s hs => P.snoc_h_le h' hanti hle hout hup hdown hcard hs
  have e2 : (P.snoc h' hanti hle hout hup hdown hcard).h N = P.h N :=
    P.snoc_h_le h' hanti hle hout hup hdown hcard le_rfl
  have e3 := P.snoc_h_succ h' hanti hle hout hup hdown hcard
  simp only [e1]
  refine prod_congr rfl fun c _ => ?_
  simp only [mem_filter]
  rw [e2, e3]

/-- **An appended path is lower than another one with the same past** when its potential after the new letter is
smaller. -/
theorem HPath.snoc_lt {Q : HPath n (N + 1) T vec B} (hQ : ∀ t ≤ N, Q.h t = P.h t)
    (hphi : ∑ c ∈ win T, wt n (h' c) < phi Q (N + 1)) :
    (P.snoc h' hanti hle hout hup hdown hcard).lt Q := by
  refine ⟨N + 1, le_rfl, fun s hs => ?_, ?_⟩
  · unfold phi
    rw [P.snoc_h_le h' hanti hle hout hup hdown hcard (by omega), hQ s (by omega)]
  · unfold phi at hphi ⊢
    rw [P.snoc_h_succ]
    exact hphi

end Snoc

/-- **Appending letters respects the order**: if `Q ≺ R` then `Q.snoc ≺ P` for any `P` extending `R`. -/
theorem HPath.lt_snoc {Q R : HPath n N T vec B} (hQR : Q.lt R) {P : HPath n (N + 1) T vec B}
    (hP : ∀ t ≤ N, P.h t = R.h t) {Q' : HPath n (N + 1) T vec B} (hQ' : ∀ t ≤ N, Q'.h t = Q.h t) : Q'.lt P := by
  obtain ⟨t, ht, h1, h2⟩ := hQR
  refine ⟨t, by omega, fun s hs => ?_, ?_⟩
  · unfold phi at h1 ⊢; rw [hQ' s (by omega), hP s (by omega)]; exact h1 s hs
  · unfold phi at h2 ⊢; rw [hQ' t ht, hP t ht]; exact h2

/-- **The first-row strip** after `N` letters: the `B_N` columns after the top. -/
def HPath.stripV (P : HPath n N T vec B) (hn : 0 < n) : Finset ℤ := Ioc (P.top hn) (P.top hn + B N)

/-- **The last-row strip** after `N` letters: the `B_N` columns up to the bottom. -/
def HPath.stripC (P : HPath n N T vec B) : Finset ℤ := Ioc (P.bot - B N) P.bot

/-- **The first-row strip lies inside the window.** -/
theorem HPath.stripV_sub (P : HPath n N T vec B) (hn : 0 < n) (hT : ∑ s ∈ range (N + 1), B s < T) :
    P.stripV hn ⊆ Ioo (-(T : ℤ)) T := fun c hc => by
  have h1 := P.top_le hn
  have h2 := (P.top_spec hn).1
  rw [sum_range_succ] at hT
  rw [HPath.stripV, mem_Ioc] at hc
  rw [mem_Ioo]
  constructor <;> omega

/-- **The last-row strip lies inside the window.** -/
theorem HPath.stripC_sub (P : HPath n N T vec B) (hn : 0 < n) (hT : ∑ s ∈ range (N + 1), B s < T) :
    P.stripC ⊆ Ioo (-(T : ℤ)) T := fun c hc => by
  have h1 := P.bot_ge hn
  obtain ⟨h2, h3, h4, h5⟩ := P.bot_spec hn
  have hTn : P.h N (T : ℤ) = 0 := by rw [P.out N le_rfl _ (by simp), h0, ite_eq_right (by omega)]
  have h6 : P.bot < T := by
    rcases lt_or_eq_of_le h3 with h | h
    · exact h
    · have := h4 _ le_rfl; rw [h] at this; omega
  rw [sum_range_succ] at hT
  rw [HPath.stripC, mem_Ioc] at hc
  rw [mem_Ioo]
  constructor <;> omega

/-- **The heights after the first-row strip.** -/
def HPath.hV (P : HPath n N T vec B) (hn : 0 < n) (c : ℤ) : ℕ := P.h N c + if c ∈ P.stripV hn then 1 else 0

/-- **The heights after the last-row strip.** -/
def HPath.hC (P : HPath n N T vec B) (c : ℤ) : ℕ := P.h N c - if c ∈ P.stripC then 1 else 0

/-- **The path extended by the first-row strip** (the letter `N` a vector letter). -/
def HPath.extV (P : HPath n N T vec B) (hn : 0 < n) (hv : vec N = true) (hT : ∑ s ∈ range (N + 1), B s < T) :
    HPath n (N + 1) T vec B :=
  P.snoc (P.hV hn)
    (by
      intro c c' hcc'
      obtain ⟨-, -, h3, h4⟩ := P.top_spec hn
      have ha := P.anti N le_rfl hcc'
      unfold HPath.hV HPath.stripV
      simp only [mem_Ioc]
      by_cases hc : c ≤ P.top hn
      · have e0 := h3 c hc
        by_cases hc' : c' ≤ P.top hn
        · split_ifs <;> omega
        · have e1 := h4 c' (by omega)
          split_ifs <;> omega
      · have e1 := h4 c (by omega)
        have e2 := h4 c' (by omega)
        split_ifs <;> omega)
    (fun c => by
      obtain ⟨-, -, -, h4⟩ := P.top_spec hn
      unfold HPath.hV HPath.stripV
      simp only [mem_Ioc]
      split_ifs with h
      · rw [h4 c h.1]; omega
      · simpa using P.le N le_rfl c)
    (fun c hc => by
      unfold HPath.hV
      rw [ite_eq_right (fun h => hc (P.stripV_sub hn hT h)), add_zero, P.out N le_rfl c hc])
    (fun _ c => by unfold HPath.hV; split_ifs <;> omega)
    (fun h => absurd hv (by simp [h]))
    (by
      have e : ((win T).filter fun c => P.h N c ≠ P.hV hn c) = P.stripV hn := by
        ext c
        unfold HPath.hV
        simp only [mem_filter]
        constructor
        · rintro ⟨-, h⟩; by_contra h'; simp [h'] at h
        · intro h; exact ⟨Ioo_subset_Icc_self (P.stripV_sub hn hT h), by simp [h]⟩
      rw [e, HPath.stripV, Int.card_Ioc]
      omega)

/-- **The path extended by the last-row strip** (the letter `N` a covector letter). -/
def HPath.extC (P : HPath n N T vec B) (hn : 0 < n) (hv : vec N = false) (hT : ∑ s ∈ range (N + 1), B s < T) :
    HPath n (N + 1) T vec B :=
  P.snoc P.hC
    (by
      intro c c' hcc'
      obtain ⟨-, -, h3, h4⟩ := P.bot_spec hn
      have ha := P.anti N le_rfl hcc'
      unfold HPath.hC HPath.stripC
      simp only [mem_Ioc]
      by_cases hc' : c' ≤ P.bot
      · have e1 := h3 c' hc'
        have e2 := h3 c (by omega)
        split_ifs <;> omega
      · have e1 := h4 c' (by omega)
        by_cases hc : c ≤ P.bot
        · have e2 := h3 c hc
          split_ifs <;> omega
        · split_ifs <;> omega)
    (fun c => by
      unfold HPath.hC
      have := P.le N le_rfl c
      omega)
    (fun c hc => by
      unfold HPath.hC
      rw [ite_eq_right (fun h => hc (P.stripC_sub hn hT h)), Nat.sub_zero, P.out N le_rfl c hc])
    (fun h => absurd hv (by simp [h]))
    (fun _ c => by
      obtain ⟨-, -, h3, -⟩ := P.bot_spec hn
      unfold HPath.hC HPath.stripC
      simp only [mem_Ioc]
      split_ifs with h
      · have := h3 c h.2; omega
      · omega)
    (by
      obtain ⟨-, -, h3, -⟩ := P.bot_spec hn
      have e : ((win T).filter fun c => P.h N c ≠ P.hC c) = P.stripC := by
        ext c
        unfold HPath.hC
        simp only [mem_filter]
        constructor
        · rintro ⟨-, h⟩; by_contra h'; simp [h'] at h
        · intro h
          refine ⟨Ioo_subset_Icc_self (P.stripC_sub hn hT h), ?_⟩
          have := h3 c (mem_Ioc.1 h).2
          simp only [h, ↓reduceIte]
          omega
      rw [e, HPath.stripC, Int.card_Ioc]
      omega)

/-- **The columns changed by the first-row strip.** -/
theorem HPath.filter_hV (P : HPath n N T vec B) (hn : 0 < n) (hT : ∑ s ∈ range (N + 1), B s < T) :
    ((win T).filter fun c => P.h N c ≠ P.hV hn c) = P.stripV hn := by
  ext c
  unfold HPath.hV
  simp only [mem_filter]
  constructor
  · rintro ⟨-, h⟩; by_contra h'; simp [h'] at h
  · intro h; exact ⟨Ioo_subset_Icc_self (P.stripV_sub hn hT h), by simp [h]⟩

/-- **The columns changed by the last-row strip.** -/
theorem HPath.filter_hC (P : HPath n N T vec B) (hn : 0 < n) (hT : ∑ s ∈ range (N + 1), B s < T) :
    ((win T).filter fun c => P.h N c ≠ P.hC c) = P.stripC := by
  obtain ⟨-, -, h3, -⟩ := P.bot_spec hn
  ext c
  unfold HPath.hC
  simp only [mem_filter]
  constructor
  · rintro ⟨-, h⟩; by_contra h'; simp [h'] at h
  · intro h
    refine ⟨Ioo_subset_Icc_self (P.stripC_sub hn hT h), ?_⟩
    have := h3 c (mem_Ioc.1 h).2
    simp only [h, ↓reduceIte]
    omega

/-- **Reindexing an interval of columns by `0, …, b − 1`.** -/
theorem prod_Ioc_eq_prod_range {M : Type*} [CommMonoid M] (m : ℤ) (b : ℕ) (f : ℕ → M) :
    ∏ c ∈ Ioc m (m + b), f (c - m - 1).toNat = ∏ i ∈ range b, f i := by
  refine prod_nbij' (fun c => (c - m - 1).toNat) (fun i => m + 1 + i) ?_ ?_ ?_ ?_ ?_
  · intro c hc; rw [mem_Ioc] at hc; rw [mem_range]; omega
  · intro i hi; rw [mem_range] at hi; rw [mem_Ioc]; omega
  · intro c hc; rw [mem_Ioc] at hc; show m + 1 + ((c - m - 1).toNat : ℤ) = c; omega
  · intro i hi; show ((m + 1 + (i : ℤ)) - m - 1).toNat = i; omega
  · intro c _; rfl

/-- **The product over the window splits** at a subset of columns. -/
theorem prod_win_split {M : Type*} [CommMonoid M] {I : Finset ℤ} (hI : I ⊆ win T) (f : ℤ → M) :
    ∏ c ∈ win T, f c = (∏ c ∈ I, f c) * ∏ c ∈ (win T).filter (· ∉ I), f c := by
  rw [← prod_filter_mul_prod_filter_not (win T) (· ∈ I)]
  congr 1
  refine prod_congr ?_ fun _ _ => rfl
  ext c; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hI h, h⟩⟩

/-- **Multiplying by a monomial of the new letter is extending by the first-row strip.** -/
theorem HPath.psi_extV (P : HPath n N T vec B) (hn : 0 < n) (hv : vec N = true)
    (hT : ∑ s ∈ range (N + 1), B s < T) (g : ℕ → Fin n) {C : ℤ → Finset (Fin n)}
    (hC : ∀ c ∈ P.stripV hn, C c = ∅) :
    psi (P.extV hn hv hT) (fun c => if c ∈ P.stripV hn then {g (c - P.top hn - 1).toNat} else C c) =
      (∏ i ∈ range (B N), X (N, g i)) * psi P C := by
  have hI : P.stripV hn ⊆ win T := fun c hc => Ioo_subset_Icc_self (P.stripV_sub hn hT hc)
  refine (HPath.psi_snoc P (P.hV hn) _ _ _ _ _ _ _).trans ?_
  rw [HPath.filter_hV P hn hT, conf, psi, prod_win_split hI, prod_win_split hI]
  rw [← prod_Ioc_eq_prod_range (P.top hn) (B N) (fun i => (X (N, g i) : MvPolynomial (ℕ × Fin n) ℤ)),
    ← mul_assoc]
  congr 1
  · rw [HPath.stripV, ← prod_mul_distrib]
    refine prod_congr rfl fun c hc => ?_
    simp only [hc, ↓reduceIte, lstep, hv]
    rw [hC c hc, wedge, sum_singleton]
    simp [sg, filter_singleton]
  · refine prod_congr rfl fun c hc => ?_
    have := (mem_filter.1 hc).2
    simp only [this, ↓reduceIte]

/-- **Multiplying by a monomial of the new letter is extending by the last-row strip**, up to a sign. -/
theorem HPath.psi_extC (P : HPath n N T vec B) (hn : 0 < n) (hv : vec N = false)
    (hT : ∑ s ∈ range (N + 1), B s < T) (g : ℕ → Fin n) {C : ℤ → Finset (Fin n)}
    (hC : ∀ c ∈ P.stripC, C c = univ) :
    psi (P.extC hn hv hT)
        (fun c => if c ∈ P.stripC then univ.erase (g (c - (P.bot - B N) - 1).toNat) else C c) =
      (∏ c ∈ P.stripC, (sg (g (c - (P.bot - B N) - 1).toNat) (univ.erase (g (c - (P.bot - B N) - 1).toNat)) :
        MvPolynomial (ℕ × Fin n) ℤ)) * ((∏ i ∈ range (B N), X (N, g i)) * psi P C) := by
  have hI : P.stripC ⊆ win T := fun c hc => Ioo_subset_Icc_self (P.stripC_sub hn hT hc)
  have hb : P.bot = P.bot - B N + B N := by ring
  refine (HPath.psi_snoc P P.hC _ _ _ _ _ _ _).trans ?_
  rw [HPath.filter_hC P hn hT, conf, psi, prod_win_split hI, prod_win_split hI]
  rw [← prod_Ioc_eq_prod_range (P.bot - B N) (B N) (fun i => (X (N, g i) : MvPolynomial (ℕ × Fin n) ℤ)), ← hb,
    ← mul_assoc, ← mul_assoc]
  congr 1
  · rw [HPath.stripC, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun c hc => ?_
    simp only [hc, ↓reduceIte, lstep, hv, Bool.false_eq_true]
    rw [hC c hc, contr]
    have e : (univ.erase (g (c - (P.bot - ↑(B N)) - 1).toNat))ᶜ = {g (c - (P.bot - ↑(B N)) - 1).toNat} := by
      ext a; simp
    rw [e, sum_singleton, insert_erase (mem_univ _)]
  · refine prod_congr rfl fun c hc => ?_
    have := (mem_filter.1 hc).2
    simp only [this, ↓reduceIte]

/-- **A product of signs times a member of a `ℤ`-submodule is a member.** -/
theorem sign_mul_mem {M : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)} {x : MvPolynomial (ℕ × Fin n) ℤ}
    (hx : x ∈ M) (k : ℕ) : (-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ k * x ∈ M := by
  rcases neg_one_pow_eq_or (MvPolynomial (ℕ × Fin n) ℤ) k with h | h
  · rw [h, one_mul]; exact hx
  · rw [h, neg_one_mul]; exact M.neg_mem hx

/-- **A product of `sg` signs is a sign.** -/
theorem prod_sg_eq {ι : Type*} (s : Finset ι) (a : ι → Fin n) (J : ι → Finset (Fin n)) :
    ∃ k : ℕ, ∏ i ∈ s, (sg (a i) (J i) : MvPolynomial (ℕ × Fin n) ℤ) = (-1) ^ k :=
  ⟨∑ i ∈ s, ((J i).filter (a i < ·)).card, by rw [← prod_pow_eq_pow_sum]; rfl⟩

/-- **Monomials of the new letter carry the lower part into the lower part** (the first-row trick):
`X_{N, g 0} ⋯ X_{N, g (B_N − 1)} · F_{≺P_{≤N}} ⊆ F_{≺P}`. -/
theorem mono_mul_lower (hn : 0 < n) (P : HPath n (N + 1) T vec B) (hT : ∑ s ∈ range (N + 1), B s < T)
    {f : MvPolynomial (ℕ × Fin n) ℤ} (hf : f ∈ lower P.trunc) (g : ℕ → Fin n) :
    (∏ i ∈ range (B N), X (N, g i)) * f ∈ lower P := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, C, rfl⟩ := hf
    cases hv : vec N
    · by_cases hC : ∀ c ∈ Q.stripC, C c = univ
      · have e := Q.psi_extC hn hv hT g hC
        obtain ⟨k, hk⟩ := prod_sg_eq Q.stripC (fun c => g (c - (Q.bot - B N) - 1).toNat)
          (fun c => univ.erase (g (c - (Q.bot - B N) - 1).toNat))
        rw [hk] at e
        have e' : (∏ i ∈ range (B N), X (N, g i)) * psi Q C =
            (-1) ^ k * psi (Q.extC hn hv hT)
              (fun c => if c ∈ Q.stripC then univ.erase (g (c - (Q.bot - B N) - 1).toNat) else C c) := by
          rw [e, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
        rw [e']
        refine sign_mul_mem (psi_mem_lower ?_ _) k
        exact HPath.lt_snoc hQ (fun t _ => rfl) (fun t ht => Q.snoc_h_le _ _ _ _ _ _ _ ht)
      · simp only [not_forall, exists_prop] at hC
        obtain ⟨c, hc, hCc⟩ := hC
        have hz : psi Q C = 0 := by
          refine prod_eq_zero (Ioo_subset_Icc_self (Q.stripC_sub hn hT hc)) ?_
          refine Q.isDeg c le_rfl _ ?_
          have := (Q.bot_spec hn).2.2.1 c (mem_Ioc.1 hc).2
          rw [this]
          intro h'
          exact hCc (eq_univ_of_card _ (by simpa using h'))
        rw [hz, mul_zero]; exact zero_mem _
    · by_cases hC : ∀ c ∈ Q.stripV hn, C c = ∅
      · rw [← Q.psi_extV hn hv hT g hC]
        refine psi_mem_lower ?_ _
        exact HPath.lt_snoc hQ (fun t _ => rfl) (fun t ht => Q.snoc_h_le _ _ _ _ _ _ _ ht)
      · simp only [not_forall, exists_prop] at hC
        obtain ⟨c, hc, hCc⟩ := hC
        have hz : psi Q C = 0 := by
          refine prod_eq_zero (Ioo_subset_Icc_self (Q.stripV_sub hn hT hc)) ?_
          refine Q.isDeg c le_rfl _ ?_
          rw [(Q.top_spec hn).2.2.2 c (mem_Ioc.1 hc).1]
          exact fun h' => hCc (card_eq_zero.1 h')
        rw [hz, mul_zero]; exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

end Ext

/-! ## Expanding the last letter -/

section Expand

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **Monomials of degree `k` in the letter `N` times a submodule.** -/
def lmon (N k : ℕ) (M : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)) : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ) :=
  Submodule.span ℤ {x | ∃ g : ℕ → Fin n, ∃ f ∈ M, x = (∏ i ∈ range k, X (N, g i)) * f}

/-- **A submodule lies in its degree-zero monomial multiples.** -/
theorem le_lmon_zero (hn : 0 < n) (M : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)) : M ≤ lmon N 0 M :=
  fun f hf => Submodule.subset_span ⟨fun _ => ⟨0, hn⟩, f, hf, by simp⟩

/-- **One more variable of the letter `N`.** -/
theorem X_mul_mem_lmon {k : ℕ} {M : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)} {x : MvPolynomial (ℕ × Fin n) ℤ}
    (hx : x ∈ lmon N k M) (a : Fin n) : X (N, a) * x ∈ lmon N (k + 1) M := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, f, hf, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun i => if i = 0 then a else g (i - 1), f, hf, ?_⟩
    rw [prod_range_succ', ← mul_assoc]
    simp [mul_comm]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a' hx

/-- **The monomials of full degree carry the lower part of the truncation into the lower part.** -/
theorem lmon_le_lower (hn : 0 < n) (P : HPath n (N + 1) T vec B) (hT : ∑ s ∈ range (N + 1), B s < T) :
    lmon N (B N) (lower P.trunc) ≤ lower P :=
  Submodule.span_le.2 fun _ ⟨g, _, hf, hx⟩ => hx ▸ mono_mul_lower hn P hT hf g

/-- **The stepped product** over the columns of `W`: the columns of `D` stepped by the letter `N`. -/
def stepProd (R : HPath n N T vec B) (W D : Finset ℤ) (C : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) ℤ :=
  ∏ c ∈ W, (if c ∈ D then lstep (vec N) N (colS R.h c N) else colS R.h c N) (C c)

/-- **A step is a signed sum over one more or one fewer coordinate.** -/
theorem lstep_eq (v : Bool) (t : ℕ) (S : Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) (V : Finset (Fin n)) :
    lstep v t S V = ∑ a ∈ (if v then V else Vᶜ), sg a V * X (t, a) *
      S (if v then V.erase a else insert a V) := by
  cases v <;> simp [lstep, wedge, contr]

/-- **The expansion of the stepped columns**: if the core `κ` times the unstepped product lies in `M` for every
filling, then `κ` times the stepped product lies in the monomials of degree `|D|` times `M`. -/
theorem stepProd_mem (hn : 0 < n) (R : HPath n N T vec B) (W : Finset ℤ) (κ : MvPolynomial (ℕ × Fin n) ℤ)
    {M : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)} (hM : ∀ C, κ * stepProd R W ∅ C ∈ M) :
    ∀ D ⊆ W, ∀ C, κ * stepProd R W D C ∈ lmon N D.card M := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _ C; exact le_lmon_zero hn M (by simpa using hM C)
  | insert c D hcD ih =>
    intro hsub C
    have hcW : c ∈ W := hsub (mem_insert_self c D)
    have ih := ih ((subset_insert c D).trans hsub)
    have hrest : ∀ C' : ℤ → Finset (Fin n), ∏ c' ∈ W.erase c,
        (if c' ∈ insert c D then lstep (vec N) N (colS R.h c' N) else colS R.h c' N) (C' c') =
        ∏ c' ∈ W.erase c, (if c' ∈ D then lstep (vec N) N (colS R.h c' N) else colS R.h c' N) (C' c') :=
      fun C' => prod_congr rfl fun c' hc' => by
        simp only [mem_insert, ne_of_mem_erase hc', false_or]
    have e1 : stepProd R W (insert c D) C = lstep (vec N) N (colS R.h c N) (C c) *
        ∏ c' ∈ W.erase c, (if c' ∈ D then lstep (vec N) N (colS R.h c' N) else colS R.h c' N) (C c') := by
      rw [stepProd, ← mul_prod_erase W _ hcW, hrest]
      simp
    have e2 : ∀ V, stepProd R W D (Function.update C c V) = colS R.h c N V *
        ∏ c' ∈ W.erase c, (if c' ∈ D then lstep (vec N) N (colS R.h c' N) else colS R.h c' N) (C c') := by
      intro V
      rw [stepProd, ← mul_prod_erase W _ hcW]
      simp only [hcD, ↓reduceIte, Function.update_self]
      congr 1
      exact prod_congr rfl fun c' hc' => by rw [Function.update_of_ne (ne_of_mem_erase hc')]
    rw [e1, lstep_eq, sum_mul, mul_sum, card_insert_of_notMem hcD]
    refine sum_mem fun a _ => ?_
    have h := ih (Function.update C c (if vec N then (C c).erase a else insert a (C c)))
    rw [e2] at h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (sg a (C c) : MvPolynomial (ℕ × Fin n) ℤ) = (-1) ^ k := ⟨_, rfl⟩
    have := sign_mul_mem (X_mul_mem_lmon h a) k
    rw [← hk] at this
    convert this using 1
    ring

end Expand

/-! ## From the Garnir relations to the exchange relations and the symmetry of equal columns -/

section Exchange

variable {n : ℕ}

/-- **Möbius inversion on the subsets of `D`.** -/
theorem moebius_powerset {α M : Type*} [DecidableEq α] [AddCommGroup M] (D : Finset α) (E : Finset α → M) :
    ∑ B' ∈ D.powerset, (-1 : ℤ) ^ (D \ B').card • ∑ D' ∈ B'.powerset, E D' = E D := by
  simp only [smul_sum]
  rw [sum_comm' (t' := D.powerset) (s' := fun D' => D.powerset.filter (D' ⊆ ·))]
  · have hin : ∀ D' ∈ D.powerset, ∑ B' ∈ D.powerset.filter (D' ⊆ ·), (-1 : ℤ) ^ (D \ B').card • E D' =
        if D' = D then E D else 0 := by
      intro D' hD'
      rw [mem_powerset] at hD'
      rw [← sum_smul]
      have hs : ∑ B' ∈ D.powerset.filter (D' ⊆ ·), (-1 : ℤ) ^ (D \ B').card =
          ∑ S ∈ (D \ D').powerset, (-1 : ℤ) ^ S.card := by
        refine sum_nbij' (fun B' => D \ B') (fun S => D \ S) ?_ ?_ ?_ ?_ ?_
        · intro B' hB'; rw [mem_filter, mem_powerset] at hB'; rw [mem_powerset]
          exact sdiff_subset_sdiff (subset_refl D) hB'.2
        · intro S hS; rw [mem_powerset] at hS; rw [mem_filter, mem_powerset]
          refine ⟨sdiff_subset, fun x hx => mem_sdiff.2 ⟨hD' hx, fun h => (mem_sdiff.1 (hS h)).2 hx⟩⟩
        · intro B' hB'; rw [mem_filter, mem_powerset] at hB'; exact Finset.sdiff_sdiff_eq_self hB'.1
        · intro S hS; rw [mem_powerset] at hS; exact Finset.sdiff_sdiff_eq_self (hS.trans sdiff_subset)
        · intro _ _; rfl
      rw [hs, sum_powerset_neg_one_pow_card]
      by_cases h : D' = D
      · subst h; simp
      · have : D \ D' ≠ ∅ := fun h' => h (subset_antisymm hD' (sdiff_eq_empty_iff_subset.1 h'))
        simp [this, h]
    rw [sum_congr rfl hin, sum_ite_eq' D.powerset D (fun _ => E D)]
    simp
  · intro B' D'
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h2.trans h1⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩

/-- **The Garnir sum of a bilinear functional** `F` of the two columns: `gar` with `S ⊗ T` replaced by `F`. -/
def garF (p : ℕ) (F : Finset (Fin n) → Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) (X Y : Finset (Fin n)) :
    MvPolynomial (ℕ × Fin n) ℤ :=
  ∑ U ∈ X.powersetCard p, sgn (X \ U) Y * sgn U (X \ U) * F U ((X \ U) ∪ Y)

/-- **The exchange sum**: the subset `D` of the right column exchanged with all subsets of the left column of the same
size. -/
def exch (F : Finset (Fin n) → Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) (A B D : Finset (Fin n)) :
    MvPolynomial (ℕ × Fin n) ℤ :=
  ∑ A1 ∈ A.powersetCard D.card, sgn ((A \ A1) ∪ D) (A1 ∪ (B \ D)) * F ((A \ A1) ∪ D) (A1 ∪ (B \ D))

/-- **The inversion count of a union**: `inv(X, Y) + inv(U, W ∪ Y) ≡ inv(W, Y) + inv(U, W)` for `X = U ⊔ W` and
`W ∩ Y = ∅`, as signs. -/
theorem sgn_shuffle {U W Y : Finset (Fin n)} (hUW : Disjoint U W) (hWY : Disjoint W Y) :
    (sgn (U ∪ W) Y : MvPolynomial (ℕ × Fin n) ℤ) * sgn U (W ∪ Y) = sgn W Y * sgn U W := by
  rw [sgn, sgn, sgn, sgn, inv_union_left hUW, inv_union_right U hWY, ← pow_add, ← pow_add]
  refine neg_one_pow_congr ?_
  omega

/-- **A Garnir sum is a sum of exchange sums**: for `A ∩ B' = ∅`,
`garF(A ∪ B', B ∖ B') = sgn(A ∪ B', B ∖ B')·Σ_{D' ⊆ B'} exch(D')`. -/
theorem garF_eq_sum_exch (p : ℕ) (F : Finset (Fin n) → Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ) {q : ℕ}
    (hF : ∀ U V, V.card ≠ q → F U V = 0) {A B B' : Finset (Fin n)} (hA : A.card = p) (hB : B.card = q)
    (hB' : B' ⊆ B) (hAB' : Disjoint A B') :
    garF p F (A ∪ B') (B \ B') = sgn (A ∪ B') (B \ B') * ∑ D' ∈ B'.powerset, exch F A B D' := by
  rw [garF, mul_sum]
  simp only [exch, mul_sum]
  rw [sum_sigma']
  refine sum_nbij' (fun U => ⟨U ∩ B', A \ U⟩) (fun x => (A \ x.2) ∪ x.1) ?_ ?_ ?_ ?_ ?_
  · intro U hU
    rw [mem_powersetCard] at hU
    simp only [mem_sigma, mem_powerset, mem_powersetCard]
    refine ⟨inter_subset_right, sdiff_subset, ?_⟩
    have h1 : (U ∩ A).card + (U ∩ B').card = p := by
      rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right hAB')), ← inter_union_distrib_left, inter_eq_left.2 hU.1, hU.2]
    have h2 : (A \ U).card + (U ∩ A).card = p := by
      rw [inter_comm, ← hA]; exact card_sdiff_add_card_inter A U
    omega
  · rintro ⟨D', A1⟩ hx
    simp only [mem_sigma, mem_powerset, mem_powersetCard] at hx
    obtain ⟨hD', hA1, hc⟩ := hx
    rw [mem_powersetCard]
    refine ⟨union_subset_union sdiff_subset hD', ?_⟩
    rw [card_union_of_disjoint (disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right hD' hAB')),
      card_sdiff_of_subset hA1, hc, hA]
    have := card_le_card hA1
    omega
  · intro U hU
    rw [mem_powersetCard] at hU
    ext x; simp only [mem_sdiff, mem_union, mem_inter, not_and, not_not]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h ‹_›
      · exact h
    · intro hxU
      rcases mem_union.1 (hU.1 hxU) with h | h
      · exact Or.inl ⟨h, fun _ => hxU⟩
      · exact Or.inr ⟨hxU, h⟩
  · rintro ⟨D', A1⟩ hx
    simp only [mem_sigma, mem_powerset, mem_powersetCard] at hx
    obtain ⟨hD', hA1, hc⟩ := hx
    simp only [Sigma.mk.injEq]
    constructor
    · ext x; simp only [mem_inter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨⟨hxA, _⟩ | h, hxB'⟩
        · exact absurd hxB' (disjoint_left.1 hAB' hxA)
        · exact h
      · intro h; exact ⟨Or.inr h, hD' h⟩
    · refine heq_of_eq ?_
      ext x; simp only [mem_sdiff, mem_union, not_or, not_and, not_not]
      constructor
      · rintro ⟨hxA, h1, -⟩; exact h1 hxA
      · intro hx; exact ⟨hA1 hx, fun _ => hx, fun h => disjoint_left.1 hAB' (hA1 hx) (hD' h)⟩
  · intro U hU
    rw [mem_powersetCard] at hU
    simp only
    -- the complement of `U` in `A ∪ B'` and the new right column
    have hW : (A ∪ B') \ U = (A \ U) ∪ (B' \ (U ∩ B')) := by
      ext x; simp only [mem_sdiff, mem_union, mem_inter]; tauto
    have hV : (A ∪ B') \ U ∪ (B \ B') = (A \ U) ∪ (B \ (U ∩ B')) := by
      ext x; simp only [mem_sdiff, mem_union, mem_inter]
      constructor
      · rintro (⟨hx, hxU⟩ | ⟨hxB, hxB'⟩)
        · rcases hx with h | h
          · exact Or.inl ⟨h, hxU⟩
          · exact Or.inr ⟨hB' h, fun h' => hxU h'.1⟩
        · exact Or.inr ⟨hxB, fun h' => hxB' h'.2⟩
      · rintro (⟨hxA, hxU⟩ | ⟨hxB, h⟩)
        · exact Or.inl ⟨Or.inl hxA, hxU⟩
        · by_cases hxB' : x ∈ B'
          · exact Or.inl ⟨Or.inr hxB', fun hxU => h ⟨hxU, hxB'⟩⟩
          · exact Or.inr ⟨hxB, hxB'⟩
    have hU' : A \ (A \ U) ∪ U ∩ B' = U := by
      ext x; simp only [mem_sdiff, mem_union, mem_inter, not_and, not_not]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h ‹_›
        · exact h
      · intro hxU
        rcases mem_union.1 (hU.1 hxU) with h | h
        · exact Or.inl ⟨h, fun _ => hxU⟩
        · exact Or.inr ⟨hxU, h⟩
    rw [hU', hV, hW]
    by_cases hd : Disjoint ((A \ U) ∪ (B' \ (U ∩ B'))) (B \ B')
    · have hUW : Disjoint U ((A \ U) ∪ (B' \ (U ∩ B'))) := by
        rw [disjoint_union_right]
        exact ⟨disjoint_sdiff, disjoint_left.2 fun x hx h => (mem_sdiff.1 h).2 (mem_inter.2 ⟨hx, (mem_sdiff.1 h).1⟩)⟩
      have e : U ∪ ((A \ U) ∪ (B' \ (U ∩ B'))) = A ∪ B' := by
        rw [← hW]; exact union_sdiff_of_subset hU.1
      have key := sgn_shuffle hUW hd
      rw [e] at key
      have hV' : (A \ U) ∪ (B' \ (U ∩ B')) ∪ (B \ B') = (A \ U) ∪ (B \ (U ∩ B')) := by rw [← hW, hV]
      rw [hV'] at key
      rw [← key]
      ring
    · -- the right column has a repeated entry: both sides vanish
      have hlt := card_union_lt hd
      have hc : ((A \ U) ∪ (B \ (U ∩ B'))).card ≠ q := by
        rw [← hV]
        have h1 : ((A ∪ B') \ U).card + (B \ B').card = q := by
          rw [card_sdiff_of_subset hU.1, card_union_of_disjoint hAB', hA, hU.2, card_sdiff_of_subset hB', hB]
          have := card_le_card hB'
          omega
        rw [← hW] at hlt
        omega
      rw [hF _ _ hc]
      ring

/-- **The exchange relation from the Garnir relations** (Möbius inversion): if every Garnir sum of `F` with `k ≥ 1`
lies in `L`, then for `D ⊆ B` disjoint from `A`, `exch(A, B, D) ≡ (−1)^{|D|}·sgn(A, B)·F(A, B)` modulo `L`. -/
theorem exch_sub_mem {p q : ℕ} (F : Finset (Fin n) → Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ)
    {L : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)} (hF : ∀ U V, V.card ≠ q → F U V = 0)
    (hGar : ∀ X Y : Finset (Fin n), p < X.card → X.card + Y.card = p + q → garF p F X Y ∈ L)
    {A B D : Finset (Fin n)} (hA : A.card = p) (hB : B.card = q) (hD : D ⊆ B) (hAD : Disjoint A D) :
    exch F A B D - (-1) ^ D.card * sgn A B * F A B ∈ L := by
  have hsum : ∀ B' ⊆ D, ∑ D' ∈ B'.powerset, exch F A B D' =
      sgn (A ∪ B') (B \ B') * garF p F (A ∪ B') (B \ B') := by
    intro B' hB'
    rw [garF_eq_sum_exch p F hF hA hB (hB'.trans hD) (disjoint_of_subset_right hB' hAD), ← mul_assoc]
    rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp
  have hE0 : exch F A B ∅ = sgn A B * F A B := by simp [exch]
  rw [← moebius_powerset D (exch F A B), ← add_sum_erase _ _ (empty_mem_powerset D)]
  rw [sdiff_empty, powerset_empty, sum_singleton, hE0]
  have : ((-1 : ℤ) ^ D.card • (sgn A B * F A B) : MvPolynomial (ℕ × Fin n) ℤ) = (-1) ^ D.card * sgn A B * F A B := by
    rw [zsmul_eq_mul]; push_cast; ring
  rw [this, add_sub_cancel_left]
  refine sum_mem fun B' hB' => ?_
  obtain ⟨hne, hB'D⟩ := mem_erase.1 hB'
  rw [mem_powerset] at hB'D
  rw [hsum B' hB'D]
  refine Submodule.smul_mem _ _ (sign_mul_mem (hGar _ _ ?_ ?_) _)
  · rw [card_union_of_disjoint (disjoint_of_subset_right hB'D hAD), hA]
    have := card_pos.2 (nonempty_iff_ne_empty.2 hne)
    omega
  · rw [card_union_of_disjoint (disjoint_of_subset_right hB'D hAD), hA, card_sdiff_of_subset (hB'D.trans hD), hB]
    have := card_le_card (hB'D.trans hD)
    omega

/-- **The entries of `B` below, above and at `a`.** -/
theorem card_lt_add_card_gt_add (B : Finset (Fin n)) (a : Fin n) :
    (B.filter (· < a)).card + (B.filter (a < ·)).card + (if a ∈ B then 1 else 0) = B.card := by
  by_cases ha : a ∈ B
  · have h1 := card_lt_add_card_gt (notMem_erase a B)
    have e1 : (B.erase a).filter (· < a) = B.filter (· < a) := by
      ext x; simp only [mem_filter, mem_erase]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.ne, h.1⟩, h.2⟩⟩
    have e2 : (B.erase a).filter (a < ·) = B.filter (a < ·) := by
      ext x; simp only [mem_filter, mem_erase]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.ne', h.1⟩, h.2⟩⟩
    rw [e1, e2] at h1
    rw [ite_eq_left ha, ← card_erase_add_one ha]
    omega
  · rw [ite_eq_right ha, add_zero]
    exact card_lt_add_card_gt ha

/-- **The inversions in both directions count the pairs of distinct entries.** -/
theorem inv_add_inv (A B : Finset (Fin n)) : inv A B + inv B A + (A ∩ B).card = A.card * B.card := by
  have hswap : inv B A = ∑ a ∈ A, (B.filter (a < ·)).card := by
    rw [inv]
    simp only [card_filter]
    exact sum_comm
  have hI : (A ∩ B).card = ∑ a ∈ A, (if a ∈ B then 1 else 0) := by
    rw [← card_filter, filter_mem_eq_inter]
  rw [hswap, inv, hI, ← sum_add_distrib, ← sum_add_distrib, card_eq_sum_ones A, sum_mul, one_mul]
  exact sum_congr rfl fun a _ => card_lt_add_card_gt_add B a

/-- **Equal columns are symmetric** modulo the Garnir relations: `F(B, A) ≡ F(A, B)`. -/
theorem symm_sub_mem {p : ℕ} (F : Finset (Fin n) → Finset (Fin n) → MvPolynomial (ℕ × Fin n) ℤ)
    {L : Submodule ℤ (MvPolynomial (ℕ × Fin n) ℤ)} (hF : ∀ U V, V.card ≠ p → F U V = 0)
    (hGar : ∀ X Y : Finset (Fin n), p < X.card → X.card + Y.card = p + p → garF p F X Y ∈ L)
    {A B : Finset (Fin n)} (hA : A.card = p) (hB : B.card = p) : F B A - F A B ∈ L := by
  have h := exch_sub_mem F hF hGar hA hB (sdiff_subset (s := B) (t := A)) disjoint_sdiff
  have hD : (B \ A).card = (A \ B).card := by
    have h1 := card_sdiff_add_card_inter A B
    have h2 := card_sdiff_add_card_inter B A
    rw [inter_comm] at h2
    omega
  have hex : exch F A B (B \ A) = sgn B A * F B A := by
    rw [exch, ← add_sum_erase _ _ (show A \ B ∈ A.powersetCard (B \ A).card from
      mem_powersetCard.2 ⟨sdiff_subset, hD.symm⟩)]
    have e1 : A \ (A \ B) ∪ B \ A = B := by
      ext x; simp only [mem_union, mem_sdiff, not_and, not_not]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h ‹_›
        · exact h
      · intro hx; by_cases hxA : x ∈ A
        · exact Or.inl ⟨hxA, fun _ => hx⟩
        · exact Or.inr ⟨hx, hxA⟩
    have e2 : A \ B ∪ B \ (B \ A) = A := by
      ext x; simp only [mem_union, mem_sdiff, not_and, not_not]
      constructor
      · rintro (⟨h, _⟩ | ⟨hxB, h⟩)
        · exact h
        · exact h hxB
      · intro hx; by_cases hxB : x ∈ B
        · exact Or.inr ⟨hxB, fun _ => hx⟩
        · exact Or.inl ⟨hx, hxB⟩
    rw [e1, e2, add_eq_left]
    refine sum_eq_zero fun A1 hA1 => ?_
    obtain ⟨hne, hA1'⟩ := mem_erase.1 hA1
    obtain ⟨hA1A, hA1c⟩ := mem_powersetCard.1 hA1'
    -- `A1` meets `B`, so the right column has a repeated entry
    have hmeet : ¬ Disjoint A1 (B \ (B \ A)) := by
      intro hd
      apply hne
      refine eq_of_subset_of_card_le (fun x hx => mem_sdiff.2 ⟨hA1A hx, fun hxB => ?_⟩) ?_
      · exact disjoint_left.1 hd hx (mem_sdiff.2 ⟨hxB, fun h => (mem_sdiff.1 h).2 (hA1A hx)⟩)
      · rw [hA1c, hD]
    have hlt := card_union_lt hmeet
    have h1 : (B \ (B \ A)).card = p - (B \ A).card := by rw [card_sdiff_of_subset sdiff_subset, hB]
    have h2 := card_le_card (sdiff_subset : B \ A ⊆ B)
    have hc : (A1 ∪ B \ (B \ A)).card ≠ p := by omega
    rw [hF _ _ hc, mul_zero]
  rw [hex] at h
  have hpar : ((-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ (B \ A).card * sgn A B) * sgn B A = 1 := by
    rw [sgn, sgn, ← pow_add, ← pow_add]
    have h1 := inv_add_inv A B
    have h2 := card_sdiff_add_card_inter B A
    rw [inter_comm] at h2
    rw [hA, hB] at h1
    have h3 : (p * p + p) % 2 = 0 := by
      have := Nat.even_mul_succ_self p
      rw [Nat.even_iff, Nat.mul_succ] at this
      exact this
    exact (neg_one_pow_congr (b := 0) (by omega)).trans (pow_zero _)
  have hm := sign_mul_mem h (inv B A)
  have hsq : (sgn B A : MvPolynomial (ℕ × Fin n) ℤ) * sgn B A = 1 := by
    rw [sgn, ← pow_add, ← two_mul, pow_mul]; simp
  have e : (-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ inv B A * (sgn B A * F B A - (-1) ^ (B \ A).card * sgn A B * F A B) =
      F B A - F A B := by
    rw [show ((-1 : MvPolynomial (ℕ × Fin n) ℤ) ^ inv B A) = sgn B A from rfl]
    calc sgn B A * (sgn B A * F B A - (-1) ^ (B \ A).card * sgn A B * F A B)
        = (sgn B A * sgn B A) * F B A - ((-1) ^ (B \ A).card * sgn A B * sgn B A) * F A B := by ring
      _ = F B A - F A B := by rw [hsq, hpar, one_mul, one_mul]
  rwa [e] at hm

end Exchange

/-! ## The Garnir relations of a path -/

section GarPath

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The window without the columns `j` and `j + 1`.** -/
def win2 (T : ℕ) (j : ℤ) : Finset ℤ := ((win T).erase (j + 1)).erase j

/-- **The Garnir sum of a path at the columns `j, j + 1`**, the other columns filled by `C`. -/
def garP (P : HPath n N T vec B) (j : ℤ) (X Y : Finset (Fin n)) (C : ℤ → Finset (Fin n)) :
    MvPolynomial (ℕ × Fin n) ℤ :=
  gar (P.h N j) (colS P.h j N) (colS P.h (j + 1) N) X Y * ∏ c ∈ win2 T j, colS P.h c N (C c)

/-- **The Garnir relations of a path**: every Garnir sum with something to shuffle (`|X| > h_j`) at two adjacent
columns of the window lies in the lower part. -/
def GarStmt (P : HPath n N T vec B) : Prop :=
  ∀ j ∈ Ico (-(T : ℤ)) T, ∀ (X Y : Finset (Fin n)) (C : ℤ → Finset (Fin n)), P.h N j < X.card →
    X.card + Y.card = P.h N j + P.h N (j + 1) → garP P j X Y C ∈ lower P

/-- **A product over the window splits off two adjacent columns.** -/
theorem prod_win_two {M : Type*} [CommMonoid M] {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (f : ℤ → M) :
    ∏ c ∈ win T, f c = f j * f (j + 1) * ∏ c ∈ win2 T j, f c := by
  rw [mem_Ico] at hj
  have h1 : j + 1 ∈ win T := mem_Icc.2 ⟨by omega, by omega⟩
  have h2 : j ∈ (win T).erase (j + 1) := mem_erase.2 ⟨by omega, mem_Icc.2 ⟨by omega, by omega⟩⟩
  rw [← mul_prod_erase _ _ h1, ← mul_prod_erase _ _ h2, win2, ← mul_assoc, mul_comm (f (j + 1))]

/-- **The two-column functional of a path**: `Ψ(P, C)` with the columns `j, j + 1` filled by `U, V`. -/
def psi2 (P : HPath n N T vec B) (j : ℤ) (C : ℤ → Finset (Fin n)) (U V : Finset (Fin n)) :
    MvPolynomial (ℕ × Fin n) ℤ :=
  colS P.h j N U * colS P.h (j + 1) N V * ∏ c ∈ win2 T j, colS P.h c N (C c)

/-- **The two-column functional is the path polynomial of the refilled path.** -/
theorem psi2_eq (P : HPath n N T vec B) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (C : ℤ → Finset (Fin n))
    (U V : Finset (Fin n)) :
    psi2 P j C U V = psi P (Function.update (Function.update C j U) (j + 1) V) := by
  rw [psi, prod_win_two hj, psi2]
  simp only [Function.update_self, ne_eq, show j ≠ j + 1 by omega, not_false_eq_true,
    Function.update_of_ne]
  congr 1
  refine prod_congr rfl fun c hc => ?_
  simp only [win2, mem_erase] at hc
  rw [Function.update_of_ne hc.2.1, Function.update_of_ne hc.1]

/-- **The Garnir sum of the two-column functional is the Garnir sum of the path.** -/
theorem garF_psi2 (P : HPath n N T vec B) (j : ℤ) (C : ℤ → Finset (Fin n)) (X Y : Finset (Fin n)) :
    garF (P.h N j) (psi2 P j C) X Y = garP P j X Y C := by
  rw [garF, garP, gar, sum_mul]
  refine sum_congr rfl fun U _ => ?_
  rw [psi2]
  ring

/-- **Equal adjacent columns of a path are symmetric** modulo the lower part. -/
theorem HPath.symm_mem (P : HPath n N T vec B) (hG : GarStmt P) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T)
    (heq : P.h N j = P.h N (j + 1)) (C : ℤ → Finset (Fin n)) (U V : Finset (Fin n)) :
    psi2 P j C V U - psi2 P j C U V ∈ lower P := by
  by_cases hU : U.card = P.h N j
  · by_cases hV : V.card = P.h N j
    · refine symm_sub_mem (psi2 P j C) (fun U' V' hV' => ?_) (fun X Y h1 h2 => ?_) hU hV
      · rw [psi2, P.isDeg (j + 1) le_rfl V' (by rw [← heq]; exact hV'), mul_zero, zero_mul]
      · rw [garF_psi2]; exact hG j hj X Y C h1 (by rw [← heq]; exact h2)
    · rw [psi2, psi2, P.isDeg j le_rfl V hV, P.isDeg (j + 1) le_rfl V (by rw [← heq]; exact hV)]
      simp
  · rw [psi2, psi2, P.isDeg j le_rfl U hU, P.isDeg (j + 1) le_rfl U (by rw [← heq]; exact hU)]
    simp

/-- **The exchange relations of a path**: for `D ⊆ V` disjoint from `U`,
`exch(U, V, D) ≡ (−1)^{|D|}·sgn(U, V)·Ψ(U, V)` modulo the lower part. -/
theorem HPath.exch_mem (P : HPath n N T vec B) (hG : GarStmt P) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T)
    (C : ℤ → Finset (Fin n)) {U V D : Finset (Fin n)} (hU : U.card = P.h N j) (hV : V.card = P.h N (j + 1))
    (hD : D ⊆ V) (hUD : Disjoint U D) :
    exch (psi2 P j C) U V D - (-1) ^ D.card * sgn U V * psi2 P j C U V ∈ lower P :=
  exch_sub_mem (psi2 P j C) (fun U' V' hV' => by rw [psi2, P.isDeg (j + 1) le_rfl V' hV', mul_zero, zero_mul])
    (fun X Y h1 h2 => by rw [garF_psi2]; exact hG j hj X Y C h1 h2) hU hV hD hUD

end GarPath

/-! ## Moving a step across equal columns, and the valid configurations -/

section Move

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The column states after one more letter**, inside the window. -/
theorem HPath.colS_succ_eq (P : HPath n (N + 1) T vec B) {c : ℤ} (hc : c ∈ win T) :
    (colS P.h c (N + 1) : Finset (Fin n) → _) =
      if c ∈ P.chg N then lstep (vec N) N (colS P.h c N) else colS P.h c N := by
  rw [colS_succ]
  unfold ustep lstep HPath.chg
  simp only [mem_filter, hc, true_and]
  have hu := P.up N (by omega)
  have hd := P.down N (by omega)
  cases hv : vec N
  · have := hd hv c
    by_cases h1 : P.h N c < P.h (N + 1) c
    · omega
    · by_cases h2 : P.h (N + 1) c < P.h N c
      · simp [h1, h2, show P.h N c ≠ P.h (N + 1) c by omega, Step.app]
      · simp [show P.h N c = P.h (N + 1) c by omega, Step.app]
  · have := hu hv c
    by_cases h1 : P.h N c < P.h (N + 1) c
    · simp [h1, show P.h N c ≠ P.h (N + 1) c by omega, Step.app]
    · by_cases h2 : P.h (N + 1) c < P.h N c
      · omega
      · simp [show P.h N c = P.h (N + 1) c by omega, Step.app]

/-- **The stepped product only sees the stepped columns inside its range.** -/
theorem stepProd_congr_set (R : HPath n N T vec B) (W : Finset ℤ) {D D' : Finset ℤ} (h : ∀ c ∈ W, c ∈ D ↔ c ∈ D')
    (C : ℤ → Finset (Fin n)) : stepProd R W D C = stepProd R W D' C :=
  prod_congr rfl fun c hc => by rw [if_congr (h c hc) rfl rfl]

/-- **A configuration splits off two adjacent columns.** -/
theorem conf_two (R : HPath n N T vec B) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (D : Finset ℤ)
    (C : ℤ → Finset (Fin n)) :
    conf R D C = (if j ∈ D then lstep (vec N) N (colS R.h j N) else colS R.h j N) (C j) *
      (if j + 1 ∈ D then lstep (vec N) N (colS R.h (j + 1) N) else colS R.h (j + 1) N) (C (j + 1)) *
        stepProd R (win2 T j) D C := by
  rw [conf, prod_win_two hj, stepProd]

/-- **The swap of two adjacent columns of a filling.** -/
def swapC (C : ℤ → Finset (Fin n)) (j : ℤ) : ℤ → Finset (Fin n) :=
  Function.update (Function.update C j (C (j + 1))) (j + 1) (C j)

/-- **Moving a step across two equal columns** (`Sym` of the truncation): if the columns `j, j + 1` have equal
heights after `N` letters and only `j + 1` is stepped, the configuration agrees, modulo the monomials times the lower
part, with the one stepping `j` instead, the two columns of the filling swapped. -/
theorem conf_move (hn : 0 < n) (R : HPath n N T vec B) (hG : GarStmt R) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T)
    (heq : R.h N j = R.h N (j + 1)) {D : Finset ℤ} (hD : D ⊆ win T) (hj1 : j + 1 ∈ D) (hj0 : j ∉ D)
    (C : ℤ → Finset (Fin n)) :
    conf R D C - conf R (insert j (D.erase (j + 1))) (swapC C j) ∈ lmon N D.card (lower R) := by
  have hne : j ≠ j + 1 := by omega
  rw [conf_two R hj, conf_two R hj]
  simp only [hj1, hj0, mem_insert_self, ↓reduceIte, mem_insert, hne.symm, mem_erase, ne_eq,
    not_true_eq_false, false_and, or_false]
  have hw : ∀ c ∈ win2 T j, swapC C j c = C c := fun c hc => by
    simp only [win2, mem_erase] at hc
    rw [swapC, Function.update_of_ne hc.2.1, Function.update_of_ne hc.1]
  have hsp : stepProd R (win2 T j) (insert j (D.erase (j + 1))) (swapC C j) =
      stepProd R (win2 T j) (D.erase (j + 1)) C := by
    rw [stepProd_congr_set R _ (D' := D.erase (j + 1)) (fun c hc => by
      simp only [win2, mem_erase] at hc
      simp [hc.1])]
    exact prod_congr rfl fun c hc => by rw [hw c hc]
  rw [hsp]
  have hs1 : swapC C j j = C (j + 1) := by
    rw [swapC, Function.update_of_ne hne, Function.update_self]
  have hs2 : swapC C j (j + 1) = C j := by rw [swapC, Function.update_self]
  have hsp2 : stepProd R (win2 T j) D C = stepProd R (win2 T j) (D.erase (j + 1)) C :=
    stepProd_congr_set R _ (fun c hc => by
      simp only [win2, mem_erase] at hc
      simp [hc.2.1]) C
  rw [hsp2, hs1, hs2, lstep_eq, lstep_eq]
  simp only [mul_sum, sum_mul]
  rw [← sum_sub_distrib]
  have hcard : D.card = (D.erase (j + 1)).card + 1 := (card_erase_add_one hj1).symm
  rw [hcard]
  refine sum_mem fun a _ => ?_
  set V := (if vec N then (C (j + 1)).erase a else insert a (C (j + 1)))
  -- the core: the symmetry of the truncation at the columns `j, j + 1`
  have hcore : ∀ C', (colS R.h j N (C j) * colS R.h (j + 1) N V - colS R.h j N V * colS R.h (j + 1) N (C j)) *
      stepProd R (win2 T j) ∅ C' ∈ lower R := by
    intro C'
    have h := R.symm_mem hG hj heq C' V (C j)
    have e : stepProd R (win2 T j) ∅ C' = ∏ c ∈ win2 T j, colS R.h c N (C' c) := by simp [stepProd]
    rw [e, sub_mul]
    simpa [psi2, mul_comm, mul_assoc, mul_left_comm] using h
  have hmem := stepProd_mem hn R (win2 T j) _ hcore (D.erase (j + 1)) (fun c hc => by
    simp only [win2, mem_erase]
    have hcD := mem_of_mem_erase hc
    exact ⟨fun h => hj0 (h ▸ hcD), ne_of_mem_erase hc, hD hcD⟩) C
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (sg a (C (j + 1)) : MvPolynomial (ℕ × Fin n) ℤ) = (-1) ^ k := ⟨_, rfl⟩
  have := sign_mul_mem (X_mul_mem_lmon hmem a) k
  rw [← hk] at this
  convert this using 1
  ring

/-- **A valid configuration of a vector letter is the path polynomial of a lower path**: if stepping the columns of
`D` (`|D| = B_N`) keeps the heights antitone and at most `n`, and lowers the potential of `P`, then the configuration
lies in the lower part of `P`. -/
theorem conf_mem_lower_of_valid_vec (R : HPath n N T vec B) (hv : vec N = true) {D : Finset ℤ}
    (hD : D ⊆ Ioo (-(T : ℤ)) T) (hcard : D.card = B N)
    (hanti : Antitone fun c => R.h N c + if c ∈ D then 1 else 0)
    (hle : ∀ c ∈ D, R.h N c < n) {P : HPath n (N + 1) T vec B} (hP : ∀ t ≤ N, P.h t = R.h t)
    (hphi : ∑ c ∈ D, (n - R.h N c) < ∑ c ∈ P.chg N, (n - R.h N c)) (hPv : ∀ c, P.h (N + 1) c = R.h N c +
      if c ∈ P.chg N then 1 else 0) (C : ℤ → Finset (Fin n)) : conf R D C ∈ lower P := by
  have hfilt : ((win T).filter fun c => R.h N c ≠ R.h N c + if c ∈ D then 1 else 0) = D := by
    ext c; simp only [mem_filter]
    constructor
    · rintro ⟨-, h⟩; by_contra h'; simp [h'] at h
    · intro h; exact ⟨Ioo_subset_Icc_self (hD h), by simp [h]⟩
  let Q := R.snoc (fun c => R.h N c + if c ∈ D then 1 else 0) hanti
    (fun c => by
      split_ifs with h
      · have := hle c h; omega
      · simpa using R.le N le_rfl c)
    (fun c hc => by rw [ite_eq_right (fun h => hc (hD h)), add_zero, R.out N le_rfl c hc])
    (fun _ c => by split_ifs <;> omega) (fun h => absurd hv (by simp [h])) (by rw [hfilt, hcard])
  have hpsi : psi Q C = conf R D C := by
    rw [HPath.psi_snoc, hfilt]
  rw [← hpsi]
  refine psi_mem_lower (HPath.snoc_lt _ _ _ _ _ _ _ _ hP ?_) C
  -- the potentials
  have hwt : ∀ k, k < n → wt n (k + 1) = wt n k + (n - k) := fun k _ => by rw [wt, sum_range_succ, wt]
  have e1 : ∑ c ∈ win T, wt n (R.h N c + if c ∈ D then 1 else 0) =
      ∑ c ∈ win T, wt n (R.h N c) + ∑ c ∈ D, (n - R.h N c) := by
    rw [← sum_filter_add_sum_filter_not (win T) (· ∈ D), ← sum_filter_add_sum_filter_not (win T) (· ∈ D)
      (fun c => wt n (R.h N c))]
    have hDw : (win T).filter (· ∈ D) = D := by
      ext c; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Ioo_subset_Icc_self (hD h), h⟩⟩
    rw [hDw]
    have h1 : ∑ c ∈ D, wt n (R.h N c + if c ∈ D then 1 else 0) = ∑ c ∈ D, wt n (R.h N c) + ∑ c ∈ D, (n - R.h N c) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun c hc => by simp only [hc, ↓reduceIte]; exact hwt _ (hle c hc)
    have h2 : ∑ c ∈ (win T).filter (· ∉ D), wt n (R.h N c + if c ∈ D then 1 else 0) =
        ∑ c ∈ (win T).filter (· ∉ D), wt n (R.h N c) :=
      sum_congr rfl fun c hc => by simp [(mem_filter.1 hc).2]
    rw [h1, h2]; ring
  have e2 : phi P (N + 1) = ∑ c ∈ win T, wt n (R.h N c) + ∑ c ∈ P.chg N, (n - R.h N c) := by
    unfold phi
    simp_rw [hPv]
    rw [← sum_filter_add_sum_filter_not (win T) (· ∈ P.chg N), ← sum_filter_add_sum_filter_not (win T)
      (· ∈ P.chg N) (fun c => wt n (R.h N c))]
    have hDw : (win T).filter (· ∈ P.chg N) = P.chg N := by
      ext c; simp only [mem_filter, HPath.chg]; tauto
    rw [hDw]
    have h1 : ∑ c ∈ P.chg N, wt n (R.h N c + if c ∈ P.chg N then 1 else 0) =
        ∑ c ∈ P.chg N, wt n (R.h N c) + ∑ c ∈ P.chg N, (n - R.h N c) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun c hc => ?_
      simp only [hc, ↓reduceIte]
      have := P.le (N + 1) le_rfl c
      rw [hPv] at this
      simp only [hc, ↓reduceIte] at this
      exact hwt _ (by omega)
    have h2 : ∑ c ∈ (win T).filter (· ∉ P.chg N), wt n (R.h N c + if c ∈ P.chg N then 1 else 0) =
        ∑ c ∈ (win T).filter (· ∉ P.chg N), wt n (R.h N c) :=
      sum_congr rfl fun c hc => by simp [(mem_filter.1 hc).2]
    rw [h1, h2]; ring
  rw [e1, e2]
  omega

end Move

/-! ## The special configurations: cascades through equal columns -/

section Cascade

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **Swapping twice is the identity.** -/
theorem swapC_swapC (C : ℤ → Finset (Fin n)) (j : ℤ) : swapC (swapC C j) j = C := by
  funext c
  unfold swapC
  by_cases h1 : c = j + 1
  · subst h1; simp
  · by_cases h2 : c = j
    · subst h2; simp
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **The changed columns lie inside the window.** -/
theorem HPath.chg_sub (P : HPath n (N + 1) T vec B) : P.chg N ⊆ Ioo (-(T : ℤ)) T := fun c hc => by
  by_contra h
  simp only [HPath.chg, mem_filter] at hc
  exact hc.2 (by rw [P.out N (by omega) c h, P.out (N + 1) le_rfl c h])

/-- **The heights after a vector letter.** -/
theorem HPath.h_succ_vec (P : HPath n (N + 1) T vec B) (hv : vec N = true) (c : ℤ) :
    P.h (N + 1) c = P.h N c + if c ∈ P.chg N then 1 else 0 := by
  have := P.up N (by omega) hv c
  by_cases hc : c ∈ win T
  · simp only [HPath.chg, mem_filter, hc, true_and]
    split_ifs <;> omega
  · have h1 : c ∉ P.chg N := fun h => hc (mem_filter.1 h).1
    rw [ite_eq_right h1, add_zero, P.out (N + 1) le_rfl c (fun h => hc (Ioo_subset_Icc_self h)),
      P.out N (by omega) c (fun h => hc (Ioo_subset_Icc_self h))]

/-- **The heights after a covector letter.** -/
theorem HPath.h_succ_cov (P : HPath n (N + 1) T vec B) (hv : vec N = false) (c : ℤ) :
    P.h (N + 1) c + (if c ∈ P.chg N then 1 else 0) = P.h N c := by
  have := P.down N (by omega) hv c
  by_cases hc : c ∈ win T
  · simp only [HPath.chg, mem_filter, hc, true_and]
    split_ifs <;> omega
  · have h1 : c ∉ P.chg N := fun h => hc (mem_filter.1 h).1
    rw [ite_eq_right h1, add_zero, P.out (N + 1) le_rfl c (fun h => hc (Ioo_subset_Icc_self h)),
      P.out N (by omega) c (fun h => hc (Ioo_subset_Icc_self h))]

/-- **Moving a step across two equal columns keeps the membership in the lower part.** -/
theorem conf_move_iff (hn : 0 < n) (P : HPath n (N + 1) T vec B) (hT : ∑ s ∈ range (N + 1), B s < T)
    (hG : GarStmt P.trunc) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (heq : P.h N j = P.h N (j + 1))
    {D : Finset ℤ} (hD : D ⊆ win T) (hcard : D.card = B N) (hj1 : j + 1 ∈ D) (hj0 : j ∉ D) :
    (∀ C, conf P.trunc D C ∈ lower P) ↔ ∀ C, conf P.trunc (insert j (D.erase (j + 1))) C ∈ lower P := by
  have hm := fun C => lmon_le_lower hn P hT
    (hcard ▸ conf_move hn P.trunc hG hj heq hD hj1 hj0 C)
  constructor
  · intro h C
    have := sub_mem (h (swapC C j)) (hm (swapC C j))
    rwa [sub_sub_cancel, swapC_swapC] at this
  · intro h C
    have := add_mem (hm C) (h (swapC C j))
    rwa [sub_add_cancel] at this

/-- **A valid configuration of a covector letter is the path polynomial of a lower path.** -/
theorem conf_mem_lower_of_valid_cov (R : HPath n N T vec B) (hv : vec N = false) {D : Finset ℤ}
    (hD : D ⊆ Ioo (-(T : ℤ)) T) (hcard : D.card = B N)
    (hanti : Antitone fun c => R.h N c - if c ∈ D then 1 else 0)
    (hge : ∀ c ∈ D, 1 ≤ R.h N c) {P : HPath n (N + 1) T vec B} (hP : ∀ t ≤ N, P.h t = R.h t)
    (hphi : ∑ c ∈ P.chg N, (n + 1 - R.h N c) < ∑ c ∈ D, (n + 1 - R.h N c))
    (hPv : ∀ c, P.h (N + 1) c + (if c ∈ P.chg N then 1 else 0) = R.h N c) (C : ℤ → Finset (Fin n)) :
    conf R D C ∈ lower P := by
  have hfilt : ((win T).filter fun c => R.h N c ≠ R.h N c - if c ∈ D then 1 else 0) = D := by
    ext c; simp only [mem_filter]
    constructor
    · rintro ⟨-, h⟩; by_contra h'; simp [h'] at h
    · intro h; have := hge c h; exact ⟨Ioo_subset_Icc_self (hD h), by simp [h]; omega⟩
  let Q := R.snoc (fun c => R.h N c - if c ∈ D then 1 else 0) hanti
    (fun c => by have := R.le N le_rfl c; omega)
    (fun c hc => by rw [ite_eq_right (fun h => hc (hD h)), Nat.sub_zero, R.out N le_rfl c hc])
    (fun h => absurd hv (by simp [h]))
    (fun _ c => by
      split_ifs with h
      · have := hge c h; omega
      · omega) (by rw [hfilt, hcard])
  have hpsi : psi Q C = conf R D C := by
    rw [HPath.psi_snoc, hfilt]
  rw [← hpsi]
  refine psi_mem_lower (HPath.snoc_lt _ _ _ _ _ _ _ _ hP ?_) C
  have hwt : ∀ k, 1 ≤ k → k ≤ n → wt n (k - 1) + (n + 1 - k) = wt n k := fun k hk _ => by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [wt, wt, sum_range_succ, Nat.add_sub_cancel]
    congr 1
    omega
  have key : ∀ D' ⊆ win T, (∀ c ∈ D', 1 ≤ R.h N c) →
      ∑ c ∈ win T, wt n (R.h N c - if c ∈ D' then 1 else 0) + ∑ c ∈ D', (n + 1 - R.h N c) =
        ∑ c ∈ win T, wt n (R.h N c) := by
    intro D' hD' hge'
    rw [← sum_filter_add_sum_filter_not (win T) (· ∈ D'), ← sum_filter_add_sum_filter_not (win T) (· ∈ D')
      (fun c => wt n (R.h N c))]
    have hDw : (win T).filter (· ∈ D') = D' := by
      ext c; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hD' h, h⟩⟩
    rw [hDw]
    have h1 : ∑ c ∈ D', wt n (R.h N c - if c ∈ D' then 1 else 0) + ∑ c ∈ D', (n + 1 - R.h N c) =
        ∑ c ∈ D', wt n (R.h N c) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun c hc => by
        simp only [hc, ↓reduceIte]; exact hwt _ (hge' c hc) (R.le N le_rfl c)
    have h2 : ∑ c ∈ (win T).filter (· ∉ D'), wt n (R.h N c - if c ∈ D' then 1 else 0) =
        ∑ c ∈ (win T).filter (· ∉ D'), wt n (R.h N c) :=
      sum_congr rfl fun c hc => by simp [(mem_filter.1 hc).2]
    rw [← h1, h2]; ring
  have e1 := key D (fun c hc => Ioo_subset_Icc_self (hD hc)) hge
  have hchg : P.chg N ⊆ win T := filter_subset _ _
  have hge2 : ∀ c ∈ P.chg N, 1 ≤ R.h N c := fun c hc => by
    have := hPv c; simp only [hc, ↓reduceIte] at this; omega
  have e2 := key (P.chg N) hchg hge2
  have e3 : phi P (N + 1) = ∑ c ∈ win T, wt n (R.h N c - if c ∈ P.chg N then 1 else 0) := by
    unfold phi
    refine sum_congr rfl fun c _ => ?_
    have := hPv c
    congr 1
    omega
  rw [e3]
  omega

end Cascade

section Special

variable {n N T : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The indicator of a set with one column added and one removed.** -/
theorem ind_insert_erase {D : Finset ℤ} {l r x : ℤ} (hl : l ∉ D) (hlr : l ≠ r) :
    (if x ∈ insert l (D.erase r) then 1 else 0 : ℕ) =
      if x = l then 1 else if x = r then 0 else if x ∈ D then 1 else 0 := by
  by_cases h1 : x = l
  · subst h1; simp
  · by_cases h2 : x = r
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- **The vector special configuration lies in the lower part**: the box of the column `j + 1` moved to the column
`j`, through the cascades of equal columns on both sides. -/
theorem special_vec (hn : 0 < n) (P : HPath n (N + 1) T vec B) (hT : ∑ s ∈ range (N + 1), B s < T)
    (hG : GarStmt P.trunc) (hv : vec N = true) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (hj0 : j ∉ P.chg N)
    (hj1 : j + 1 ∈ P.chg N) (hlt : P.h N j < n) (C : ℤ → Finset (Fin n)) :
    conf P.trunc (insert j ((P.chg N).erase (j + 1))) C ∈ lower P := by
  set D := P.chg N with hDdef
  have hDw : D ⊆ win T := fun c hc => Ioo_subset_Icc_self (P.chg_sub hc)
  have hcardD : D.card = B N := P.card N (by omega)
  have hPa : ∀ c, P.h N (c + 1) + (if c + 1 ∈ D then 1 else 0) ≤ P.h N c + if c ∈ D then 1 else 0 := by
    intro c
    have := P.anti (N + 1) le_rfl (show c ≤ c + 1 by omega)
    rwa [P.h_succ_vec hv, P.h_succ_vec hv] at this
  have hRa : ∀ c c', c ≤ c' → P.h N c' ≤ P.h N c := fun c c' h => P.anti N (by omega) h
  have hHH : P.h N (j + 1) < P.h N j := by
    have := hPa j; simp only [hj0, hj1, ↓reduceIte] at this; omega
  set H := P.h N j with hHdef
  set H' := P.h N (j + 1) with hH'def
  have hTm : P.h N (-(T : ℤ)) = n := P.h_neg (by omega)
  -- the left end of the cascade
  have hexL : ∃ k : ℕ, ¬ ∀ i ∈ Icc (j - (k + 1 : ℕ)) j, P.h N i = H ∧ i ∉ D := by
    refine ⟨(j + T).toNat, fun h => ?_⟩
    have := (h (-(T : ℤ)) (mem_Icc.2 ⟨by rw [mem_Ico] at hj; omega, by rw [mem_Ico] at hj; omega⟩)).1
    omega
  classical
  let k := Nat.find hexL
  have hk : ∀ i ∈ Icc (j - k) j, P.h N i = H ∧ i ∉ D := by
    intro i hi
    by_cases hk0 : k = 0
    · rw [hk0, Nat.cast_zero, sub_zero, Icc_self, mem_singleton] at hi
      subst hi; exact ⟨rfl, hj0⟩
    · have := not_not.1 (Nat.find_min hexL (show k - 1 < k by omega))
      exact this i (by rw [show ((k - 1 + 1 : ℕ) : ℤ) = k by omega]; exact hi)
  have hk' : P.h N (j - k - 1) ≠ H ∨ j - k - 1 ∈ D := by
    have := Nat.find_spec hexL
    by_contra hc
    rw [not_or, not_not] at hc
    apply this
    intro i hi
    rw [mem_Icc] at hi
    by_cases hi' : i = j - k - 1
    · subst hi'; exact hc
    · exact hk i (mem_Icc.2 ⟨by omega, hi.2⟩)
  set l := j - k with hldef
  -- the right end of the cascade
  have hexR : ∃ m : ℕ, ¬ ∀ t ∈ Icc (j + 1) (j + 1 + (m + 1 : ℕ)), P.h N t = H' ∧ t ∈ D := by
    refine ⟨(T - j).toNat, fun h => ?_⟩
    have := (h (T : ℤ) (mem_Icc.2 ⟨by rw [mem_Ico] at hj; omega, by rw [mem_Ico] at hj; omega⟩)).2
    have := P.chg_sub this
    simp at this
  let m := Nat.find hexR
  have hm : ∀ t ∈ Icc (j + 1) (j + 1 + m), P.h N t = H' ∧ t ∈ D := by
    intro t ht
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero, add_zero, Icc_self, mem_singleton] at ht
      subst ht; exact ⟨rfl, hj1⟩
    · have := not_not.1 (Nat.find_min hexR (show m - 1 < m by omega))
      exact this t (by rw [show ((m - 1 + 1 : ℕ) : ℤ) = m by omega]; exact ht)
  have hm' : P.h N (j + 1 + m + 1) ≠ H' ∨ j + 1 + m + 1 ∉ D := by
    have := Nat.find_spec hexR
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    apply this
    intro t ht
    rw [mem_Icc] at ht
    by_cases ht' : t = j + 1 + m + 1
    · subst ht'; exact hc
    · exact hm t (mem_Icc.2 ⟨ht.1, by push_cast at ht; omega⟩)
  set r := j + 1 + m with hrdef
  have hlD : l ∉ D := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).2
  have hrD : r ∈ D := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).2
  have hlr : l ≠ r := by omega
  have hlT : -(T : ℤ) < l := by
    by_contra hc
    have := hRa l (-(T : ℤ)) (by omega)
    have := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).1
    omega
  have hL : ∀ c, c + 1 = l → P.h N (c + 1) + 1 ≤ P.h N c + if c ∈ D then 1 else 0 := by
    intro c hc
    have hl := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).1
    have hcl : c = l - 1 := by omega
    have h2 := hRa c (c + 1) (by omega)
    rw [hc] at h2 ⊢
    rw [hcl] at h2 ⊢
    rcases hk' with h | h
    · split_ifs <;> omega
    · simp only [h, ↓reduceIte]; omega
  have hR : ∀ c, c = r → P.h N (c + 1) + (if c + 1 ∈ D then 1 else 0) ≤ P.h N c := by
    intro c hc
    have hr := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).1
    have h2 := hRa c (c + 1) (by omega)
    rw [hc] at h2 ⊢
    rcases hm' with h | h
    · split_ifs <;> omega
    · simp only [h, ↓reduceIte]; omega
  -- (1) the end of both cascades is valid
  have hvalid : ∀ C, conf P.trunc (insert l (D.erase r)) C ∈ lower P := by
    intro C
    refine conf_mem_lower_of_valid_vec P.trunc hv (D := insert l (D.erase r)) ?_ ?_ ?_ ?_ (fun t _ => rfl) ?_
      (P.h_succ_vec hv) C
    · intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · rw [mem_Ioo]; rw [mem_Ico] at hj; omega
      · exact P.chg_sub (mem_of_mem_erase hc)
    · rw [card_insert_of_notMem (fun h => hlD (mem_of_mem_erase h)), card_erase_of_mem hrD, hcardD]
      have : 0 < B N := hcardD ▸ card_pos.2 ⟨_, hrD⟩
      omega
    · refine antitone_int_of_succ_le fun c => ?_
      show P.h N (c + 1) + _ ≤ P.h N c + _
      rw [ind_insert_erase hlD hlr, ind_insert_erase hlD hlr]
      have h1 := hPa c
      have h2 := hRa c (c + 1) (by omega)
      by_cases hc1 : c + 1 = l
      · have hc2 : c ≠ l := by omega
        have hc3 : c ≠ r := by omega
        rw [ite_eq_left hc1, ite_eq_right hc2,
          ite_eq_right hc3]
        exact hL c hc1
      · by_cases hc2 : c = l
        · rw [ite_eq_right hc1, ite_eq_left hc2]
          split_ifs <;> omega
        · by_cases hc3 : c = r
          · have hr1 : c + 1 ≠ r := by omega
            rw [ite_eq_right hc1, ite_eq_right hr1,
              ite_eq_right hc2, ite_eq_left hc3]
            simpa using hR c hc3
          · rw [ite_eq_right hc1, ite_eq_right hc2,
              ite_eq_right hc3]
            by_cases hr1 : c + 1 = r
            · rw [ite_eq_left hr1]
              have : (if c ∈ D then 1 else 0) ≥ 0 := Nat.zero_le _
              omega
            · rw [ite_eq_right hr1]
              exact h1
    · intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · show P.h N l < n
        rw [(hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).1]; exact hlt
      · have := P.le (N + 1) le_rfl c
        rw [P.h_succ_vec hv, ite_eq_left (mem_of_mem_erase hc)] at this
        show P.h N c < n
        omega
    · rw [← add_sum_erase _ _ hrD, sum_insert (fun h => hlD (mem_of_mem_erase h))]
      have := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).1
      have := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).1
      show n - P.h N l + _ < n - P.h N r + _
      omega
  -- (2) the right cascade
  have hright : ∀ i ≤ m, ∀ C, conf P.trunc (insert l (D.erase (r - i))) C ∈ lower P := by
    intro i
    induction i with
    | zero => intro _; simpa using hvalid
    | succ i ih =>
      intro hi
      set t := r - (i + 1 : ℕ) with htdef
      have ht1 : t + 1 = r - i := by rw [htdef]; push_cast; ring
      have htD : t ∈ D := (hm t (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have htD1 : t + 1 ∈ D := (hm (t + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have heq : P.h N t = P.h N (t + 1) := by
        rw [(hm t (mem_Icc.2 ⟨by omega, by omega⟩)).1,
          (hm (t + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1]
      have htI : t ∈ Ico (-(T : ℤ)) T := by
        have := mem_Ioo.1 (P.chg_sub hrD); rw [mem_Ico]; rw [mem_Ico] at hj; omega
      have hcfg := conf_move_iff hn P hT hG htI heq
        (D := insert l (D.erase t))
        (fun c hc => by
          rcases mem_insert.1 hc with rfl | hc
          · rw [mem_Icc]; rw [mem_Ico] at hj; omega
          · exact hDw (mem_of_mem_erase hc))
        (by rw [card_insert_of_notMem (fun h => hlD (mem_of_mem_erase h)), card_erase_of_mem htD, hcardD]
            have : 0 < B N := hcardD ▸ card_pos.2 ⟨_, htD⟩
            omega)
        (mem_insert.2 (Or.inr (mem_erase.2 ⟨by omega, htD1⟩)))
        (by simp only [mem_insert, mem_erase, not_or]; exact ⟨by omega, by simp⟩)
      have hset : insert t ((insert l (D.erase t)).erase (t + 1)) = insert l (D.erase (t + 1)) := by
        ext x; simp only [mem_insert, mem_erase]
        constructor
        · rintro (rfl | ⟨h1, rfl | ⟨h2, h3⟩⟩)
          · exact Or.inr ⟨by omega, htD⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h3⟩
        · rintro (rfl | ⟨h1, h3⟩)
          · exact Or.inr ⟨by omega, Or.inl rfl⟩
          · by_cases hx : x = t
            · exact Or.inl hx
            · exact Or.inr ⟨h1, Or.inr ⟨hx, h3⟩⟩
      rw [hset, ht1] at hcfg
      exact hcfg.2 (ih (by omega))
  -- (3) the left cascade
  have hleft : ∀ i ≤ k, ∀ C, conf P.trunc (insert (l + i) (D.erase (j + 1))) C ∈ lower P := by
    intro i
    induction i with
    | zero => intro _ C; have := hright m le_rfl C; simpa [r] using this
    | succ i ih =>
      intro hi
      set s := l + i with hsdef
      have hs0 : s ∉ D := (hk s (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have hs1 : s + 1 ∉ D := (hk (s + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have heq : P.h N s = P.h N (s + 1) := by
        rw [(hk s (mem_Icc.2 ⟨by omega, by omega⟩)).1,
          (hk (s + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1]
      have hcfg := conf_move_iff hn P hT hG (j := s) (by rw [mem_Ico] at hj ⊢; omega) heq
        (D := insert (s + 1) (D.erase (j + 1)))
        (fun c hc => by
          rcases mem_insert.1 hc with rfl | hc
          · rw [mem_Icc]; rw [mem_Ico] at hj; omega
          · exact hDw (mem_of_mem_erase hc))
        (by rw [card_insert_of_notMem (fun h => hs1 (mem_of_mem_erase h)), card_erase_of_mem hj1, hcardD]
            have : 0 < B N := hcardD ▸ card_pos.2 ⟨_, hj1⟩
            omega)
        (mem_insert_self _ _)
        (by simp only [mem_insert, mem_erase, not_or]; exact ⟨by omega, fun h => hs0 h.2⟩)
      have hset : insert s ((insert (s + 1) (D.erase (j + 1))).erase (s + 1)) = insert s (D.erase (j + 1)) := by
        rw [erase_insert (fun h => hs1 (mem_of_mem_erase h))]
      rw [hset] at hcfg
      have e : l + ((i + 1 : ℕ) : ℤ) = s + 1 := by rw [hsdef]; push_cast; ring
      rw [e]
      exact hcfg.2 (ih (by omega))
  have := hleft k le_rfl C
  rwa [show l + (k : ℤ) = j by omega] at this


/-- **The covector special configuration lies in the lower part**: the removal at the column `j` moved to the column
`j + 1`, through the cascades of equal columns on both sides. -/
theorem special_cov (hn : 0 < n) (P : HPath n (N + 1) T vec B) (hT : ∑ s ∈ range (N + 1), B s < T)
    (hG : GarStmt P.trunc) (hv : vec N = false) {j : ℤ} (hj : j ∈ Ico (-(T : ℤ)) T) (hj0 : j ∈ P.chg N)
    (hj1 : j + 1 ∉ P.chg N) (hge : 1 ≤ P.h N (j + 1)) (C : ℤ → Finset (Fin n)) :
    conf P.trunc (insert (j + 1) ((P.chg N).erase j)) C ∈ lower P := by
  set D := P.chg N with hDdef
  have hDw : D ⊆ win T := fun c hc => Ioo_subset_Icc_self (P.chg_sub hc)
  have hcardD : D.card = B N := P.card N (by omega)
  have hPa : ∀ c, P.h N (c + 1) + (if c ∈ D then 1 else 0) ≤ P.h N c + if c + 1 ∈ D then 1 else 0 := by
    intro c
    have := P.anti (N + 1) le_rfl (show c ≤ c + 1 by omega)
    have h1 : P.h (N + 1) c + (if c ∈ D then 1 else 0) = P.h N c := P.h_succ_cov hv c
    have h2 : P.h (N + 1) (c + 1) + (if c + 1 ∈ D then 1 else 0) = P.h N (c + 1) := P.h_succ_cov hv (c + 1)
    omega
  have hRa : ∀ c c', c ≤ c' → P.h N c' ≤ P.h N c := fun c c' h => P.anti N (by omega) h
  have hHH : P.h N (j + 1) < P.h N j := by
    have := hPa j; simp only [hj0, hj1, ↓reduceIte] at this; omega
  set H := P.h N j with hHdef
  set H' := P.h N (j + 1) with hH'def
  have hTp : P.h N (T : ℤ) = 0 := by rw [P.out N (by omega) _ (by simp), h0, ite_eq_right (by omega)]
  classical
  -- the left end: the run of removed columns of height `H` ending at `j`
  have hexL : ∃ k : ℕ, ¬ ∀ i ∈ Icc (j - (k + 1 : ℕ)) j, P.h N i = H ∧ i ∈ D := by
    refine ⟨(j + T).toNat, fun h => ?_⟩
    have := (h (-(T : ℤ)) (mem_Icc.2 ⟨by rw [mem_Ico] at hj; omega, by rw [mem_Ico] at hj; omega⟩)).2
    have := P.chg_sub this
    simp at this
  let k := Nat.find hexL
  have hk : ∀ i ∈ Icc (j - k) j, P.h N i = H ∧ i ∈ D := by
    intro i hi
    by_cases hk0 : k = 0
    · rw [hk0, Nat.cast_zero, sub_zero, Icc_self, mem_singleton] at hi
      subst hi; exact ⟨rfl, hj0⟩
    · have := not_not.1 (Nat.find_min hexL (show k - 1 < k by omega))
      exact this i (by rw [show ((k - 1 + 1 : ℕ) : ℤ) = k by omega]; exact hi)
  have hk' : P.h N (j - k - 1) ≠ H ∨ j - k - 1 ∉ D := by
    have := Nat.find_spec hexL
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    apply this
    intro i hi
    rw [mem_Icc] at hi
    by_cases hi' : i = j - k - 1
    · subst hi'; exact hc
    · exact hk i (mem_Icc.2 ⟨by push_cast at hi; omega, hi.2⟩)
  set l := j - k with hldef
  -- the right end: the run of kept columns of height `H'` starting at `j + 1`
  have hexR : ∃ m : ℕ, ¬ ∀ t ∈ Icc (j + 1) (j + 1 + (m + 1 : ℕ)), P.h N t = H' ∧ t ∉ D := by
    refine ⟨(T - j).toNat, fun h => ?_⟩
    have := (h (T : ℤ) (mem_Icc.2 ⟨by rw [mem_Ico] at hj; omega, by rw [mem_Ico] at hj; omega⟩)).1
    omega
  let m := Nat.find hexR
  have hm : ∀ t ∈ Icc (j + 1) (j + 1 + m), P.h N t = H' ∧ t ∉ D := by
    intro t ht
    by_cases hm0 : m = 0
    · rw [hm0, Nat.cast_zero, add_zero, Icc_self, mem_singleton] at ht
      subst ht; exact ⟨rfl, hj1⟩
    · have := not_not.1 (Nat.find_min hexR (show m - 1 < m by omega))
      exact this t (by rw [show ((m - 1 + 1 : ℕ) : ℤ) = m by omega]; exact ht)
  have hm' : P.h N (j + 1 + m + 1) ≠ H' ∨ j + 1 + m + 1 ∈ D := by
    have := Nat.find_spec hexR
    by_contra hc
    rw [not_or, not_not] at hc
    apply this
    intro t ht
    rw [mem_Icc] at ht
    by_cases ht' : t = j + 1 + m + 1
    · subst ht'; exact hc
    · exact hm t (mem_Icc.2 ⟨ht.1, by push_cast at ht; omega⟩)
  set r := j + 1 + m with hrdef
  have hlD : l ∈ D := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).2
  have hrD : r ∉ D := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).2
  have hrl : r ≠ l := by omega
  have hlI := mem_Ioo.1 (P.chg_sub hlD)
  have hrT : r < T := by
    by_contra hc
    have := hRa (T : ℤ) r (by omega)
    have := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).1
    omega
  have hL : ∀ c, c + 1 = l → P.h N (c + 1) ≤ P.h N c - if c ∈ D then 1 else 0 := by
    intro c hc
    have hl := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).1
    have hcl : c = l - 1 := by omega
    have h2 := hRa c (c + 1) (by omega)
    rw [hc] at h2 ⊢
    rw [hcl] at h2 ⊢
    rcases hk' with h | h
    · split_ifs <;> omega
    · simp only [h, ↓reduceIte]; omega
  have hR : ∀ c, c = r → P.h N (c + 1) - (if c + 1 ∈ D then 1 else 0) ≤ P.h N c - 1 := by
    intro c hc
    have hr := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).1
    have h2 := hRa c (c + 1) (by omega)
    rw [hc] at h2 ⊢
    rcases hm' with h | h
    · split_ifs <;> omega
    · simp only [h, ↓reduceIte]; omega
  -- (1) the end of both cascades is valid
  have hvalid : ∀ C, conf P.trunc (insert r (D.erase l)) C ∈ lower P := by
    intro C
    refine conf_mem_lower_of_valid_cov P.trunc hv (D := insert r (D.erase l)) ?_ ?_ ?_ ?_ (fun t _ => rfl) ?_
      (P.h_succ_cov hv) C
    · intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · rw [mem_Ioo]; rw [mem_Ico] at hj; omega
      · exact P.chg_sub (mem_of_mem_erase hc)
    · rw [card_insert_of_notMem (fun h => hrD (mem_of_mem_erase h)), card_erase_of_mem hlD, hcardD]
      have : 0 < B N := hcardD ▸ card_pos.2 ⟨_, hlD⟩
      omega
    · refine antitone_int_of_succ_le fun c => ?_
      show P.h N (c + 1) - _ ≤ P.h N c - _
      rw [ind_insert_erase hrD hrl, ind_insert_erase hrD hrl]
      have h1 := hPa c
      have h2 := hRa c (c + 1) (by omega)
      by_cases hc1 : c + 1 = l
      · have hc2 : c ≠ l := by omega
        have hc3 : c ≠ r := by omega
        have hc4 : c + 1 ≠ r := by omega
        rw [ite_eq_right hc4, ite_eq_left hc1, ite_eq_right hc3, ite_eq_right hc2]
        have := hL c hc1
        omega
      · by_cases hc3 : c = r
        · have hr1 : c + 1 ≠ r := by omega
          have hc2 : c + 1 ≠ l := hc1
          rw [ite_eq_right hr1, ite_eq_right hc2, ite_eq_left hc3]
          exact hR c hc3
        · rw [ite_eq_right hc3]
          by_cases hr1 : c + 1 = r
          · rw [ite_eq_left hr1]
            by_cases hc2 : c = l
            · rw [ite_eq_left hc2]; omega
            · rw [ite_eq_right hc2]
              split_ifs with h4
              · have := (hm (c + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1
                have h5 : c = j := by
                  by_contra h6
                  exact (hm c (mem_Icc.2 ⟨by omega, by omega⟩)).2 h4
                rw [h5] at h4 ⊢
                omega
              · omega
          · rw [ite_eq_right hr1, ite_eq_right hc1]
            by_cases hc2 : c = l
            · rw [ite_eq_left hc2]
              omega
            · rw [ite_eq_right hc2]
              split_ifs at h1 ⊢ <;> omega
    · intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · show 1 ≤ P.h N r
        rw [(hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).1]; exact hge
      · have : P.h (N + 1) c + (if c ∈ D then 1 else 0) = P.h N c := P.h_succ_cov hv c
        rw [ite_eq_left (mem_of_mem_erase hc)] at this
        show 1 ≤ P.h N c
        omega
    · rw [← add_sum_erase _ _ hlD, sum_insert (fun h => hrD (mem_of_mem_erase h))]
      have := (hk l (mem_Icc.2 ⟨le_rfl, by omega⟩)).1
      have := (hm r (mem_Icc.2 ⟨by omega, le_rfl⟩)).1
      have := P.le N (by omega) l
      show n + 1 - P.h N l + _ < n + 1 - P.h N r + _
      omega
  -- (2) the left cascade: the kept column moves from `l` to `j`
  have hleft : ∀ i ≤ k, ∀ C, conf P.trunc (insert r (D.erase (l + i))) C ∈ lower P := by
    intro i
    induction i with
    | zero => intro _; simpa using hvalid
    | succ i ih =>
      intro hi
      set s := l + i with hsdef
      have hs0 : s ∈ D := (hk s (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have hs1 : s + 1 ∈ D := (hk (s + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have heq : P.h N s = P.h N (s + 1) := by
        rw [(hk s (mem_Icc.2 ⟨by omega, by omega⟩)).1, (hk (s + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1]
      have hsI : s ∈ Ico (-(T : ℤ)) T := by
        have := mem_Ioo.1 (P.chg_sub hs0); rw [mem_Ico]; omega
      have hcfg := conf_move_iff hn P hT hG hsI heq (D := insert r (D.erase s))
        (fun c hc => by
          rcases mem_insert.1 hc with rfl | hc
          · rw [mem_Icc]; rw [mem_Ico] at hj; omega
          · exact hDw (mem_of_mem_erase hc))
        (by rw [card_insert_of_notMem (fun h => hrD (mem_of_mem_erase h)), card_erase_of_mem hs0, hcardD]
            have : 0 < B N := hcardD ▸ card_pos.2 ⟨_, hs0⟩
            omega)
        (mem_insert.2 (Or.inr (mem_erase.2 ⟨by omega, hs1⟩)))
        (by simp only [mem_insert, mem_erase, not_or]; exact ⟨by omega, by simp⟩)
      have hset : insert s ((insert r (D.erase s)).erase (s + 1)) = insert r (D.erase (s + 1)) := by
        ext x; simp only [mem_insert, mem_erase]
        constructor
        · rintro (rfl | ⟨h1, rfl | ⟨h2, h3⟩⟩)
          · exact Or.inr ⟨by omega, hs0⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h3⟩
        · rintro (rfl | ⟨h1, h3⟩)
          · exact Or.inr ⟨by omega, Or.inl rfl⟩
          · by_cases hx : x = s
            · exact Or.inl hx
            · exact Or.inr ⟨h1, Or.inr ⟨hx, h3⟩⟩
      rw [hset] at hcfg
      have e : l + ((i + 1 : ℕ) : ℤ) = s + 1 := by rw [hsdef]; push_cast; ring
      rw [e]
      exact hcfg.1 (ih (by omega))
  -- (3) the right cascade: the removal moves from `r` back to `j + 1`
  have hright : ∀ i ≤ m, ∀ C, conf P.trunc (insert (r - i) (D.erase j)) C ∈ lower P := by
    intro i
    induction i with
    | zero => intro _ C; have := hleft k le_rfl C; simpa [l] using this
    | succ i ih =>
      intro hi
      set t := r - (i + 1 : ℕ) with htdef
      have ht1 : t + 1 = r - i := by rw [htdef]; push_cast; ring
      have ht0 : t ∉ D := (hm t (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have htD1 : t + 1 ∉ D := (hm (t + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).2
      have heq : P.h N t = P.h N (t + 1) := by
        rw [(hm t (mem_Icc.2 ⟨by omega, by omega⟩)).1, (hm (t + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1]
      have htI : t ∈ Ico (-(T : ℤ)) T := by rw [mem_Ico]; rw [mem_Ico] at hj; omega
      have hcfg := conf_move_iff hn P hT hG htI heq (D := insert (t + 1) (D.erase j))
        (fun c hc => by
          rcases mem_insert.1 hc with rfl | hc
          · rw [mem_Icc]; rw [mem_Ico] at hj; omega
          · exact hDw (mem_of_mem_erase hc))
        (by rw [card_insert_of_notMem (fun h => htD1 (mem_of_mem_erase h)), card_erase_of_mem hj0, hcardD]
            have : 0 < B N := hcardD ▸ card_pos.2 ⟨_, hj0⟩
            omega)
        (mem_insert_self _ _)
        (by simp only [mem_insert, mem_erase, not_or]; exact ⟨by omega, fun h => ht0 h.2⟩)
      have hset : insert t ((insert (t + 1) (D.erase j)).erase (t + 1)) = insert t (D.erase j) := by
        rw [erase_insert (fun h => htD1 (mem_of_mem_erase h))]
      rw [hset, ht1] at hcfg
      exact hcfg.1 (ih (by omega))
  have := hright m le_rfl C
  rwa [show r - (m : ℤ) = j + 1 by omega] at this

end Special

end

end PathSpan
