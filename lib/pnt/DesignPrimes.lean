import SharpInputs
import PairSetting

/-!
# The split primes of the design

A step of the proof of the sharp frontier (`SharpInputs`, the field `SharpPieces.params`): the two split primes
`g₀ ≠ g₁` of a design (`SharpDesign.g₀`, `SharpDesign.g₁`), as the archive takes them: large primes of norm one
modulo `N` whose exceptional sets are disjoint.

**Exceptional primes.** A prime `ℓ` is exceptional for `g` at `e` (`Exc g e ℓ`) if it carries more than a quarter of
`g^e − 1`: `ℓ^{4 v_ℓ(g^e − 1)} > g^e`. The exceptional set `ExcSet r g` is `g` with the primes exceptional for `g` at
some `1 ≤ e ≤ r`. For `g ≥ 2` and `e ≥ 1` there are at most three exceptional primes (`card_exc_le`): the prime
powers `ℓ^{v_ℓ(g^e − 1)}` of distinct `ℓ` multiply to at most `g^e − 1`, and each exceeds `g^{e/4}`. So
`ExcSet r g` is finite with at most `3r + 1` elements (`exists_finset_excSet`).

**The split primes** (`exists_split_primes`, from `ShortNorm`): for `0 < ε < 1/52` and `x` large, given `d` prime,
`d ≡ 3 (mod 4)`, `d ≥ 100`, `d ∣ N`, `log N ≤ 3x^{ε/5} log² x`, `k ≥ 1` and `r ≤ 3x^{9/2+10ε}`, there are distinct
primes `g₀, g₁` in `[K^8, 2K^8]`, `K = k·exp(x^ε)`, with `4g = α² + dβ²`, `N ∣ β`, `α ≡ β + 2 (mod 2N)` (`g = ππ̄`,
`π ≡ 1 mod N`) and `ExcSet r g₀ ∩ ExcSet r g₁ = ∅`. For such a prime, `(−d/g) = 1` (`jacobiSym_neg_d_of_norm`):
`g ∤ β`, as `g ∣ β` would give `g² ∣ 4g`, and then `−d ≡ (α/β)²` modulo `g`.

**Route.**
* `ShortNorm` at `Y = K^8`, `h = 1`, `M = N` counts at least `c′Y/((4dN²)^A log Y)` primes of the shape in
  `(Y, 2Y]`. Its condition `log(4dN²) ≤ c√(log Y)` holds as `log(4dN²) ≤ 3 + 9x^{ε/5}log² x` and
  `log Y ≥ 8x^ε`.
* Given `g₀`, a `g₁` is bad if it lies in `ExcSet r g₀` or has an exceptional prime `ℓ ∈ ExcSet r g₀` at some
  `e ≤ r`. For fixed `ℓ` and `e` the bad `g ∈ (K^8, 2K^8]` have `g^e ≡ 1` modulo `Q = ℓ^{v₀}`, the least power with
  `Q^4 > K^8` (`card_exc_window_le`). There are at most `2e` such residues (`card_pow_eq_one_le`): `(ℤ/ℓ^v)ˣ` is
  cyclic for odd `ℓ` (Mathlib's `ZMod.isCyclic_units_of_prime_pow`), and for `ℓ = 2` its quotient by `±1` is
  cyclic (`isCyclic_He`). So at most `2e(2K^8/Q + 1) ≤ 6eK^6` bad `g` for each pair, and `(3r + 1)³K^6` in all
  (`exists_disjoint_excSet`).
* The count beats it once `8000x^{15}exp(A(3 + 9x^{ε/5}log² x)) < c′exp(x^ε)` (`eventually_split_big`), as
  `(3r + 1)³ ≤ 1000x^{15}`, `(4dN²)^A ≤ exp(A(3 + 9x^{ε/5}log² x))`, `log Y ≤ 8K` and `K ≥ exp(x^ε)`.

**Choices.**
* The window's lower count needs only `k ≥ 1`; no upper bound on `k` is used.
* `N > 0` is a hypothesis: for `N = 0` no prime has the shape.
* `jacobiSym_neg_d_of_norm` takes `d ≥ 9` and `d ∣ β` (both available for the design's primes, as `d ∣ N ∣ β`)
  in place of `g ∤ d`: they give `g ∤ β`, hence `g ∤ d`.
-/

open Filter Finset

namespace ZetaBalance

/-! ## Exceptional primes -/

/-- **A prime exceptional for `g` at `e`**: a prime `ℓ` carrying more than a quarter of `g^e − 1`, i.e.
`ℓ^{4 v_ℓ(g^e − 1)} > g^e`. -/
def Exc (g e ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ e < ℓ ^ (4 * padicValNat ℓ (g ^ e - 1))

/-- `Exc g e` is decidable. -/
instance (g e : ℕ) : DecidablePred (Exc g e) := fun _ => by unfold Exc; infer_instance

/-- **The exceptional set of `g` up to `r`**: `g` and the primes exceptional for `g` at some `1 ≤ e ≤ r`. -/
def ExcSet (r g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ e, 1 ≤ e ∧ e ≤ r ∧ Exc g e ℓ}

/-- For `g > 0`, a prime exceptional for `g` at `e` divides `g^e − 1`, and `g^e < (ℓ^{v_ℓ(g^e − 1)})^4`. -/
theorem Exc.dvd {g e ℓ : ℕ} (h : Exc g e ℓ) (hg : 0 < g) :
    ℓ ∣ g ^ e - 1 ∧ g ^ e < (ℓ ^ padicValNat ℓ (g ^ e - 1)) ^ 4 := by
  refine ⟨dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 fun h0 => ?_), by rw [← pow_mul']; exact h.2⟩
  have h1 := h.2
  rw [h0, mul_zero, pow_zero] at h1
  have := Nat.one_le_pow e g hg
  omega

/-- For `g ≥ 2` and `e ≥ 1`, a prime exceptional for `g` at `e` is below `g^e`. -/
theorem Exc.lt {g e ℓ : ℕ} (h : Exc g e ℓ) (hg : 2 ≤ g) (he : 1 ≤ e) : ℓ < g ^ e := by
  have hge : 2 ≤ g ^ e := hg.trans (Nat.le_self_pow (by omega) g)
  have := Nat.le_of_dvd (by omega) (h.dvd (by omega)).1
  omega

/-- **At most three exceptional primes** (finset form), for `g ≥ 2` and `e ≥ 1`: with `M = g^e − 1`, the prime
powers `ℓ^{v_ℓ(M)}` of the exceptional `ℓ` multiply to at most `M` (a sub-product of `M`'s factorisation), and each
has fourth power above `g^e`, so `(g^e + 1)^{#} ≤ M^4 < (g^e + 1)^4`. -/
theorem card_exc_le {g e : ℕ} (hg : 2 ≤ g) (he : 1 ≤ e) : ((range (g ^ e)).filter (Exc g e)).card ≤ 3 := by
  set F := (range (g ^ e)).filter (Exc g e)
  have hge : 2 ≤ g ^ e := hg.trans (Nat.le_self_pow (by omega) g)
  set M := g ^ e - 1
  have hM0 : M ≠ 0 := by omega
  have hmem : ∀ ℓ ∈ F, ℓ.Prime ∧ ℓ ≤ M ∧ g ^ e + 1 ≤ (ℓ ^ padicValNat ℓ M) ^ 4 := fun ℓ hℓ => by
    have hexc := (Finset.mem_filter.1 hℓ).2
    obtain ⟨hdvd, hlt⟩ := hexc.dvd (by omega)
    exact ⟨hexc.1, Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hdvd, hlt⟩
  have hprod : ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ M ≤ M :=
    calc ∏ ℓ ∈ F, ℓ ^ padicValNat ℓ M ≤ ∏ ℓ ∈ (range (M + 1)).filter Nat.Prime, ℓ ^ padicValNat ℓ M :=
          Finset.prod_le_prod_of_subset_of_one_le (fun ℓ hℓ => Finset.mem_filter.2
            ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hmem ℓ hℓ).2.1), (hmem ℓ hℓ).1⟩)
            (fun ℓ hℓ _ => Nat.one_le_pow _ _ (Finset.mem_filter.1 hℓ).2.pos)
      _ = M := Nat.prod_pow_prime_padicValNat M hM0 (M + 1) (Nat.lt_succ_self M)
  have hlt : (g ^ e + 1) ^ F.card < (g ^ e + 1) ^ 4 :=
    calc (g ^ e + 1) ^ F.card = ∏ _ℓ ∈ F, (g ^ e + 1) := (Finset.prod_const _).symm
      _ ≤ ∏ ℓ ∈ F, (ℓ ^ padicValNat ℓ M) ^ 4 :=
          Finset.prod_le_prod fun ℓ hℓ => (hmem ℓ hℓ).2.2
      _ = (∏ ℓ ∈ F, ℓ ^ padicValNat ℓ M) ^ 4 := Finset.prod_pow _ _ _
      _ ≤ M ^ 4 := Nat.pow_le_pow_left hprod 4
      _ < (g ^ e + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have := (Nat.pow_lt_pow_iff_right (by omega)).1 hlt
  omega

/-- **The exceptional set is finite, with at most `3r + 1` elements**, for `g ≥ 2`: it is `g` with the exceptional
primes at `e = 1, …, r`, at most three for each `e` (`card_exc_le`), all below `g^e`. -/
theorem exists_finset_excSet (r : ℕ) {g : ℕ} (hg : 2 ≤ g) :
    ∃ F : Finset ℕ, (F : Set ℕ) = ExcSet r g ∧ F.card ≤ 3 * r + 1 := by
  refine ⟨insert g ((Icc 1 r).biUnion fun e => (range (g ^ e)).filter (Exc g e)), ?_, ?_⟩
  · ext ℓ
    simp only [ExcSet, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_Icc,
      Finset.mem_filter, Finset.mem_range, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨e, ⟨he1, her⟩, -, hexc⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨e, he1, her, hexc⟩
    · rintro (rfl | ⟨e, he1, her, hexc⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨e, ⟨he1, her⟩, hexc.lt hg he1, hexc⟩
  · calc (insert g ((Icc 1 r).biUnion fun e => (range (g ^ e)).filter (Exc g e))).card
        ≤ ((Icc 1 r).biUnion fun e => (range (g ^ e)).filter (Exc g e)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ e ∈ Icc 1 r, ((range (g ^ e)).filter (Exc g e)).card) + 1 := by
          gcongr; exact Finset.card_biUnion_le
      _ ≤ (∑ _e ∈ Icc 1 r, 3) + 1 := by
          gcongr with e he; exact card_exc_le hg (Finset.mem_Icc.1 he).1
      _ = 3 * r + 1 := by simp [Finset.sum_const, Nat.card_Icc, mul_comm]

/-! ## Roots of unity modulo a prime power -/

/-- **At most `2e` solutions of `x^e = 1`** in a finite commutative group whose quotient by `⟨z⟩`, `z² = 1`, is
cyclic: `x ↦ (x mod ⟨z⟩, [x = rep])` is injective (a class is `{rep, rep·z}`), with image among the solutions in
the quotient, at most `e` of them (Mathlib's `IsCyclic.card_pow_eq_one_le`). -/
theorem card_pow_eq_one_le_of_isCyclic_quot {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (z : G)
    (hz : z ^ 2 = 1) [IsCyclic (G ⧸ Subgroup.zpowers z)] {e : ℕ} (he : 0 < e) :
    (univ.filter fun x : G => x ^ e = 1).card ≤ 2 * e := by
  classical
  set H := Subgroup.zpowers z
  have hH : ∀ y ∈ H, y = 1 ∨ y = z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hz
    rw [zpow_eq_zpow_emod k hz2]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  have key : ∀ w w' : G, (w : G ⧸ H) = w' → w = (w' : G ⧸ H).out ∨ w = (w' : G ⧸ H).out * z := by
    intro w w' hw
    have : (((w' : G ⧸ H).out : G) : G ⧸ H) = w := by rw [QuotientGroup.out_eq', hw]
    rcases hH _ (QuotientGroup.eq.1 this) with h | h
    · left; rw [inv_mul_eq_one] at h; exact h.symm
    · right; rw [inv_mul_eq_iff_eq_mul] at h; exact h
  let f : G → (G ⧸ H) × Bool := fun x => ((x : G ⧸ H), decide (x = (x : G ⧸ H).out))
  calc (univ.filter fun x : G => x ^ e = 1).card
      ≤ ((univ.filter fun y : G ⧸ H => y ^ e = 1) ×ˢ (univ : Finset Bool)).card := by
        refine Finset.card_le_card_of_injOn f (fun x hx => ?_) (fun x _ x' _ hxx => ?_)
        · have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
          refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩,
            Finset.mem_univ _⟩)
          show (x : G ⧸ H) ^ e = 1
          rw [← QuotientGroup.mk_pow, hx', QuotientGroup.mk_one]
        · have h1 : (x : G ⧸ H) = x' := (Prod.ext_iff.1 hxx).1
          have h2 : decide (x = (x : G ⧸ H).out) = decide (x' = (x' : G ⧸ H).out) := (Prod.ext_iff.1 hxx).2
          rw [h1] at h2
          have hiff := decide_eq_decide.1 h2
          by_cases hxo : x = (x' : G ⧸ H).out
          · exact hxo.trans (hiff.1 hxo).symm
          · exact ((key x x' h1).resolve_left hxo).trans
              ((key x' x' rfl).resolve_left fun h => hxo (hiff.2 h)).symm
    _ = (univ.filter fun y : G ⧸ H => y ^ e = 1).card * 2 := by simp [Finset.card_product]
    _ ≤ e * 2 := by gcongr; exact IsCyclic.card_pow_eq_one_le he
    _ = 2 * e := mul_comm _ _

/-- **At most `2e` solutions of `u^e = 1` in `(ℤ/ℓ^v)ˣ`**, `ℓ` prime: the group is cyclic unless `ℓ = 2` and
`v ≥ 3` (Mathlib's `ZMod.isCyclic_units_of_prime_pow`, `ZMod.isCyclic_units_two_pow_iff`), and for `ℓ = 2`, `v ≥ 2`
its quotient by `±1` is cyclic (`isCyclic_He`). -/
theorem card_units_pow_eq_one_le {ℓ : ℕ} (hℓ : ℓ.Prime) (v : ℕ) [NeZero (ℓ ^ v)] {e : ℕ} (he : 0 < e) :
    (univ.filter fun u : (ZMod (ℓ ^ v))ˣ => u ^ e = 1).card ≤ 2 * e := by
  by_cases h2 : ℓ = 2 ∧ 2 ≤ v
  · obtain ⟨rfl, hv⟩ := h2
    obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le' hv
    have := isCyclic_He w
    exact card_pow_eq_one_le_of_isCyclic_quot (-1) neg_one_sq he
  · have : IsCyclic (ZMod (ℓ ^ v))ˣ := by
      by_cases hℓ2 : ℓ = 2
      · subst hℓ2; exact (ZMod.isCyclic_units_two_pow_iff v).2 (by omega)
      · exact ZMod.isCyclic_units_of_prime_pow ℓ hℓ hℓ2 v
    exact (IsCyclic.card_pow_eq_one_le he).trans (by omega)

/-- **At most `2e` solutions of `x^e = 1` in `ℤ/ℓ^v`**, `ℓ` prime: each is a unit (`Units.ofPowEqOne`), so this is
`card_units_pow_eq_one_le`. -/
theorem card_pow_eq_one_le {ℓ : ℕ} (hℓ : ℓ.Prime) (v : ℕ) [NeZero (ℓ ^ v)] {e : ℕ} (he : 0 < e) :
    (univ.filter fun x : ZMod (ℓ ^ v) => x ^ e = 1).card ≤ 2 * e :=
  calc (univ.filter fun x : ZMod (ℓ ^ v) => x ^ e = 1).card
      ≤ ((univ.filter fun u : (ZMod (ℓ ^ v))ˣ => u ^ e = 1).image Units.val).card := by
        refine Finset.card_le_card fun x hx => ?_
        have hx' := (Finset.mem_filter.1 hx).2
        exact Finset.mem_image.2 ⟨Units.ofPowEqOne x e hx' he.ne', Finset.mem_filter.2 ⟨Finset.mem_univ _,
          Units.pow_ofPowEqOne hx' he.ne'⟩, Units.val_ofPowEqOne x e hx' he.ne'⟩
    _ ≤ _ := Finset.card_image_le
    _ ≤ 2 * e := card_units_pow_eq_one_le hℓ v he

/-- **The `g ≤ B` with `g^e ≡ 1 (mod ℓ^v)`**: at most `2e(⌊B/ℓ^v⌋ + 1)`, as `g ↦ (g mod ℓ^v, ⌊g/ℓ^v⌋)` is injective
into the solutions of `x^e = 1` (`card_pow_eq_one_le`) times `[0, ⌊B/ℓ^v⌋]`. -/
theorem card_pow_eq_one_window_le {ℓ : ℕ} (hℓ : ℓ.Prime) (v : ℕ) {e : ℕ} (he : 0 < e) (B : ℕ) :
    ((range (B + 1)).filter fun g : ℕ => (g : ZMod (ℓ ^ v)) ^ e = 1).card ≤ 2 * e * (B / ℓ ^ v + 1) := by
  have : NeZero (ℓ ^ v) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  calc ((range (B + 1)).filter fun g : ℕ => (g : ZMod (ℓ ^ v)) ^ e = 1).card
      ≤ ((univ.filter fun x : ZMod (ℓ ^ v) => x ^ e = 1) ×ˢ range (B / ℓ ^ v + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun g => ((g : ZMod (ℓ ^ v)), g / ℓ ^ v)) (fun g hg => ?_)
          (fun g _ g' _ hgg => ?_)
        · obtain ⟨hgB, hge⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hg)
          exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hge⟩,
            Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right
              (Nat.lt_succ_iff.1 (Finset.mem_range.1 hgB))))⟩)
        · have h1 : (g : ZMod (ℓ ^ v)) = g' := (Prod.ext_iff.1 hgg).1
          have h2 : g / ℓ ^ v = g' / ℓ ^ v := (Prod.ext_iff.1 hgg).2
          have h3 := (ZMod.natCast_eq_natCast_iff' g g' (ℓ ^ v)).1 h1
          rw [← Nat.div_add_mod g (ℓ ^ v), ← Nat.div_add_mod g' (ℓ ^ v), h2, h3]
    _ = (univ.filter fun x : ZMod (ℓ ^ v) => x ^ e = 1).card * (B / ℓ ^ v + 1) := by
        rw [Finset.card_product, Finset.card_range]
    _ ≤ 2 * e * (B / ℓ ^ v + 1) := Nat.mul_le_mul_right _ (card_pow_eq_one_le hℓ v he)

/-! ## The bad `g₁` -/

/-- **Few `g ∈ (K^8, 2K^8]` have a given exceptional prime `ℓ` at `e ≥ 1`**: at most `6eK^6`. For such `g`,
`ℓ^{4v} > g^e > K^8` with `v = v_ℓ(g^e − 1)`, so `Q = ℓ^{v₀}` divides `g^e − 1` for the least `v₀` with
`ℓ^{4v₀} > K^8`; then `Q > K²`, and `card_pow_eq_one_window_le` gives at most `2e(2K^8/Q + 1) ≤ 6eK^6`. -/
theorem card_exc_window_le {K : ℝ} (hK : 1 ≤ K) (ℓ : ℕ) {e : ℕ} (he : 1 ≤ e) :
    ((((range (⌊2 * K ^ 8⌋₊ + 1)).filter fun g : ℕ => K ^ 8 < g).filter fun g => Exc g e ℓ).card : ℝ) ≤
      6 * e * K ^ 6 := by
  by_cases hℓ : ℓ.Prime
  swap
  · have : (((range (⌊2 * K ^ 8⌋₊ + 1)).filter fun g : ℕ => K ^ 8 < g).filter fun g => Exc g e ℓ) = ∅ :=
      Finset.filter_false_of_mem fun g _ h => hℓ h.1
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hex : ∃ v : ℕ, K ^ 8 < (ℓ : ℝ) ^ (4 * v) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K ^ 8) hℓ1
    exact ⟨n, hn.trans_le (pow_le_pow_right₀ hℓ1.le (by omega))⟩
  set B := ⌊2 * K ^ 8⌋₊
  set v₀ := Nat.find hex with hv₀
  have hK0 : 0 < K := by linarith
  have hQ : (K ^ 2) ^ 4 < ((ℓ ^ v₀ : ℕ) : ℝ) ^ 4 := by
    have := Nat.find_spec hex
    rw [← hv₀, pow_mul'] at this
    push_cast
    rw [← pow_mul]
    exact this
  have hQK : K ^ 2 < ((ℓ ^ v₀ : ℕ) : ℝ) :=
    lt_of_pow_lt_pow_left₀ 4 (Nat.cast_nonneg _) hQ
  have hsub : (((range (B + 1)).filter fun g : ℕ => K ^ 8 < g).filter fun g => Exc g e ℓ) ⊆
      (range (B + 1)).filter fun g : ℕ => (g : ZMod (ℓ ^ v₀)) ^ e = 1 := by
    intro g hg
    obtain ⟨hg1, hexc⟩ := Finset.mem_filter.1 hg
    obtain ⟨hgB, hgK⟩ := Finset.mem_filter.1 hg1
    refine Finset.mem_filter.2 ⟨hgB, ?_⟩
    have hg0 : 0 < g := by exact_mod_cast (by positivity : (0 : ℝ) < K ^ 8).trans hgK
    obtain ⟨hdvd, hlt⟩ := hexc.dvd hg0
    have hmin : v₀ ≤ padicValNat ℓ (g ^ e - 1) := Nat.find_min' hex <| by
      calc K ^ 8 < g := hgK
        _ ≤ ((g ^ e : ℕ) : ℝ) := by exact_mod_cast Nat.le_self_pow (by omega) g
        _ < (ℓ : ℝ) ^ (4 * padicValNat ℓ (g ^ e - 1)) := by rw [pow_mul']; exact_mod_cast hlt
    have hQd : ℓ ^ v₀ ∣ g ^ e - 1 := (pow_dvd_pow ℓ hmin).trans pow_padicValNat_dvd
    have h1 : 1 ≤ g ^ e := Nat.one_le_pow _ _ hg0
    have := (ZMod.natCast_eq_zero_iff _ _).2 hQd
    rwa [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at this
  have hcount := (Finset.card_le_card hsub).trans (card_pow_eq_one_window_le hℓ v₀ (by omega) B)
  have hBQ : ((B / ℓ ^ v₀ : ℕ) : ℝ) ≤ 2 * K ^ 6 :=
    calc ((B / ℓ ^ v₀ : ℕ) : ℝ) ≤ (B : ℝ) / ((ℓ ^ v₀ : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ 2 * K ^ 8 / K ^ 2 :=
          div_le_div₀ (by positivity) (Nat.floor_le (by positivity)) (by positivity) hQK.le
      _ = 2 * K ^ 6 := by field_simp
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  calc ((((range (B + 1)).filter fun g : ℕ => K ^ 8 < g).filter fun g => Exc g e ℓ).card : ℝ)
      ≤ ((2 * e * (B / ℓ ^ v₀ + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = 2 * e * (((B / ℓ ^ v₀ : ℕ) : ℝ) + 1) := by push_cast; ring
    _ ≤ 2 * e * (2 * K ^ 6 + K ^ 6) := by gcongr
    _ = 6 * e * K ^ 6 := by ring

/-- **Two primes with disjoint exceptional sets**, from a large set `G` of integers `g ≥ 2` in `(K^8, 2K^8]`:
if `#G > (3r + 1)³K^6`, then some `g₀ ≠ g₁` in `G` have `ExcSet r g₀ ∩ ExcSet r g₁ = ∅`. Given any `g₀ ∈ G`, the
bad `g₁` lie in `ExcSet r g₀` (at most `3r + 1`, `exists_finset_excSet`) or have an exceptional prime
`ℓ ∈ ExcSet r g₀` at some `e ≤ r` (at most `6eK^6` for each pair, `card_exc_window_le`). -/
theorem exists_disjoint_excSet {K : ℝ} (hK : 1 ≤ K) (r : ℕ) {G : Set ℕ}
    (hG : ∀ g ∈ G, 2 ≤ g ∧ K ^ 8 < g ∧ (g : ℝ) ≤ 2 * K ^ 8) (hcard : (3 * r + 1 : ℝ) ^ 3 * K ^ 6 < G.ncard) :
    ∃ g₀ ∈ G, ∃ g₁ ∈ G, g₀ ≠ g₁ ∧ Disjoint (ExcSet r g₀) (ExcSet r g₁) := by
  have hpos : G.ncard ≠ 0 := by
    have : (0 : ℝ) < G.ncard := (by positivity : (0 : ℝ) ≤ (3 * r + 1 : ℝ) ^ 3 * K ^ 6).trans_lt hcard
    exact_mod_cast this.ne'
  obtain ⟨g₀, hg₀⟩ := Set.nonempty_of_ncard_ne_zero hpos
  obtain ⟨F₀, hF₀, hF₀c⟩ := exists_finset_excSet r (hG g₀ hg₀).1
  set W := (range (⌊2 * K ^ 8⌋₊ + 1)).filter fun g : ℕ => K ^ 8 < g
  set Bad := F₀ ∪ F₀.biUnion fun ℓ => (Icc 1 r).biUnion fun e => W.filter fun g => Exc g e ℓ
  have hBadc : (Bad.card : ℝ) ≤ (3 * r + 1) ^ 3 * K ^ 6 := by
    have h1 : Bad.card ≤ F₀.card + ∑ ℓ ∈ F₀, ∑ e ∈ Icc 1 r, (W.filter fun g => Exc g e ℓ).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)) _)
    have h2 : ∀ ℓ, ∀ e ∈ Icc 1 r, ((W.filter fun g => Exc g e ℓ).card : ℝ) ≤ 6 * r * K ^ 6 := by
      intro ℓ e he
      obtain ⟨he1, her⟩ := Finset.mem_Icc.1 he
      exact (card_exc_window_le hK ℓ he1).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast her) (by norm_num)) (by positivity))
    have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    calc (Bad.card : ℝ)
        ≤ F₀.card + ∑ ℓ ∈ F₀, ∑ e ∈ Icc 1 r, ((W.filter fun g => Exc g e ℓ).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ (3 * r + 1) + ∑ _ℓ ∈ F₀, ∑ _e ∈ Icc 1 r, 6 * r * K ^ 6 := by
          gcongr with ℓ _ e he
          · exact_mod_cast hF₀c
          · exact h2 ℓ e he
      _ = (3 * r + 1) + F₀.card * (r * (6 * r * K ^ 6)) := by simp [Finset.sum_const, Nat.card_Icc]
      _ ≤ (3 * r + 1) + (3 * r + 1) * (r * (6 * r * K ^ 6)) := by
          gcongr
          exact_mod_cast hF₀c
      _ ≤ (3 * r + 1) * K ^ 6 + (3 * r + 1) * (r * (6 * r * K ^ 6)) := by
          gcongr
          exact le_mul_of_one_le_right (by positivity) hK6
      _ = (3 * r + 1) * (1 + 6 * r ^ 2) * K ^ 6 := by ring
      _ ≤ (3 * r + 1) * (3 * r + 1) ^ 2 * K ^ 6 := by gcongr; nlinarith
      _ = (3 * r + 1) ^ 3 * K ^ 6 := by ring
  have hsub : ¬ G ⊆ ↑Bad := fun h => by
    have := Set.ncard_le_ncard h Bad.finite_toSet
    rw [Set.ncard_coe_finset] at this
    have : (G.ncard : ℝ) ≤ Bad.card := by exact_mod_cast this
    linarith
  obtain ⟨g₁, hg₁, hg₁B⟩ := Set.not_subset.1 hsub
  have hF₀B : ∀ ℓ ∈ ExcSet r g₀, ℓ ∈ Bad := fun ℓ hℓ =>
    Finset.mem_union_left _ (by rw [← Finset.mem_coe, hF₀]; exact hℓ)
  refine ⟨g₀, hg₀, g₁, hg₁, fun h => hg₁B (h ▸ hF₀B g₀ (Or.inl rfl)), ?_⟩
  rw [Set.disjoint_left]
  rintro ℓ hℓ₀ (hℓ₁ | ⟨e, he1, her, hexc⟩)
  · rw [Set.mem_singleton_iff] at hℓ₁
    subst hℓ₁
    exact hg₁B (hF₀B _ hℓ₀)
  · obtain ⟨-, hgK, hg2K⟩ := hG g₁ hg₁
    refine hg₁B (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨ℓ, ?_, Finset.mem_biUnion.2
      ⟨e, Finset.mem_Icc.2 ⟨he1, her⟩, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨?_, hgK⟩, hexc⟩⟩⟩))
    · rw [← Finset.mem_coe, hF₀]; exact hℓ₀
    · exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hg2K))

/-! ## The split primes -/

/-- **The size conditions of the split primes hold for large `x`**, for constants `A, c, c′ > 0` (those of
`ShortNorm`) and `ε > 0`: `x ≥ 1`, `3 + 9x^{ε/5}log² x ≤ 2c·x^{ε/2}` and
`8000x^{15}·exp(A(3 + 9x^{ε/5}log² x)) < c′·exp(x^ε)`. With `u = x^{ε/20}` and `log x ≤ (20/ε)u`, the left sides are
at most constant multiples of `u^6`, against `u^{10}` and `u^{20}` on the right (in logarithms for the second). -/
theorem eventually_split_big {A c c' ε : ℝ} (hA : 0 < A) (hc : 0 < c) (hc' : 0 < c') (hε : 0 < ε) :
    ∀ᶠ x in atTop, 1 ≤ x ∧ 3 + 9 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * c * x ^ (ε / 2) ∧
      8000 * x ^ 15 * Real.exp (A * (3 + 9 * x ^ (ε / 5) * Real.log x ^ 2)) < c' * Real.exp (x ^ ε) := by
  set K₁ := 20 / ε with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  set C₁ := 3 + 9 * K₁ ^ 2 with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  set D := |Real.log 8000 - Real.log c'| + 15 * K₁ + A * C₁ with hD
  filter_upwards [eventually_ge_atTop 1, (tendsto_rpow_atTop (show 0 < ε / 20 by positivity)).eventually_ge_atTop
    (max 1 (max (C₁ / (2 * c)) (D + 1)))] with x hx hu
  have hx0 : 0 < x := by linarith
  set u := x ^ (ε / 20) with hu_def
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have huC : C₁ / (2 * c) ≤ u := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hu
  have huD : D + 1 ≤ u := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hu
  have hpow : ∀ n : ℕ, x ^ ((n : ℝ) * (ε / 20)) = u ^ n := fun n => by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm]
  have h5 : x ^ (ε / 5) = u ^ 4 := by rw [← hpow]; norm_num; ring_nf
  have h2 : x ^ (ε / 2) = u ^ 10 := by rw [← hpow]; norm_num; ring_nf
  have h1 : x ^ ε = u ^ 20 := by rw [← hpow]; norm_num; ring_nf
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x ≤ K₁ * u :=
    calc Real.log x ≤ u / (ε / 20) := Real.log_le_rpow_div hx0.le (by positivity)
      _ = K₁ * u := by rw [hK₁]; field_simp
  have hu6 : u ≤ u ^ 6 := le_self_pow₀ hu1 (by norm_num)
  have hu61 : 1 ≤ u ^ 6 := one_le_pow₀ hu1
  have hB : 3 + 9 * x ^ (ε / 5) * Real.log x ^ 2 ≤ C₁ * u ^ 6 := by
    rw [h5]
    have e2 : Real.log x ^ 2 ≤ (K₁ * u) ^ 2 := pow_le_pow_left₀ hl0 hl 2
    calc 3 + 9 * u ^ 4 * Real.log x ^ 2 ≤ 3 + 9 * u ^ 4 * (K₁ * u) ^ 2 := by gcongr
      _ = 3 + 9 * K₁ ^ 2 * u ^ 6 := by ring
      _ ≤ 3 * u ^ 6 + 9 * K₁ ^ 2 * u ^ 6 := by gcongr; linarith
      _ = C₁ * u ^ 6 := by rw [hC₁]; ring
  refine ⟨hx, ?_, ?_⟩
  · have hC : C₁ ≤ 2 * c * u ^ 4 := by
      have h := (div_le_iff₀ (by positivity)).1 huC
      have hu4 : u ≤ u ^ 4 := le_self_pow₀ hu1 (by norm_num)
      nlinarith
    calc 3 + 9 * x ^ (ε / 5) * Real.log x ^ 2 ≤ C₁ * u ^ 6 := hB
      _ ≤ 2 * c * u ^ 4 * u ^ 6 := by gcongr
      _ = 2 * c * x ^ (ε / 2) := by rw [h2]; ring
  · have hkey : Real.log 8000 + 15 * Real.log x + A * (3 + 9 * x ^ (ε / 5) * Real.log x ^ 2) <
        Real.log c' + x ^ ε := by
      have habs := le_abs_self (Real.log 8000 - Real.log c')
      have hD0 : 0 ≤ D := by positivity
      have hu14 : u ≤ u ^ 14 := le_self_pow₀ hu1 (by norm_num)
      calc Real.log 8000 + 15 * Real.log x + A * (3 + 9 * x ^ (ε / 5) * Real.log x ^ 2)
          ≤ Real.log c' + |Real.log 8000 - Real.log c'| + 15 * (K₁ * u) + A * (C₁ * u ^ 6) := by
            gcongr; linarith
        _ ≤ Real.log c' + D * u ^ 6 := by
            rw [hD]; nlinarith [abs_nonneg (Real.log 8000 - Real.log c')]
        _ < Real.log c' + (D + 1) * u ^ 6 := by nlinarith
        _ ≤ Real.log c' + u ^ 14 * u ^ 6 := by gcongr; linarith
        _ = Real.log c' + x ^ ε := by rw [h1]; ring
    have hx15 : x ^ 15 = Real.exp (15 * Real.log x) := by
      rw [show (15 : ℝ) * Real.log x = Real.log (x ^ 15) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    calc 8000 * x ^ 15 * Real.exp (A * (3 + 9 * x ^ (ε / 5) * Real.log x ^ 2))
        = Real.exp (Real.log 8000 + 15 * Real.log x + A * (3 + 9 * x ^ (ε / 5) * Real.log x ^ 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num), hx15]
      _ < Real.exp (Real.log c' + x ^ ε) := Real.exp_lt_exp.2 hkey
      _ = c' * Real.exp (x ^ ε) := by rw [Real.exp_add, Real.exp_log hc']

/-- **The split primes** (from `ShortNorm`): for `0 < ε < 1/52` there is `x₀` such that for `x ≥ x₀`, `d` prime,
`d ≡ 3 (mod 4)`, `d ≥ 100`, `0 < N` with `d ∣ N` and `log N ≤ 3x^{ε/5}log² x`, `k ≥ 1` and `r ≤ 3x^{9/2+10ε}`, there
are distinct primes `g₀, g₁` in `[K^8, 2K^8]`, `K = k·exp(x^ε)`, of norm one modulo `N` (`4g = α² + dβ²`, `N ∣ β`,
`α ≡ β + 2 (mod 2N)`), with disjoint exceptional sets `ExcSet r g₀`, `ExcSet r g₁`. -/
theorem exists_split_primes (hS : ShortNorm) : ∀ ε : ℝ, 0 < ε → ε < 1 / 52 → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (d N r k : ℕ),
    d.Prime → d % 4 = 3 → 100 ≤ d → d ∣ N → 0 < N → Real.log N ≤ 3 * x ^ (ε / 5) * Real.log x ^ 2 → 1 ≤ k →
    (r : ℝ) ≤ 3 * x ^ (9 / 2 + 10 * ε) → ∃ g₀ g₁ : ℕ, g₀.Prime ∧ g₁.Prime ∧ g₀ ≠ g₁ ∧ (∀ g ∈ [g₀, g₁],
      ((k : ℝ) * Real.exp (x ^ ε)) ^ 8 ≤ g ∧ (g : ℝ) ≤ 2 * ((k : ℝ) * Real.exp (x ^ ε)) ^ 8 ∧
      ∃ α β : ℤ, 4 * (g : ℤ) = α ^ 2 + d * β ^ 2 ∧ (N : ℤ) ∣ β ∧ α ≡ β + 2 [ZMOD 2 * N]) ∧
      Disjoint (ExcSet r g₀) (ExcSet r g₁) := by
  obtain ⟨A, c, c', hA, hc, hc', H⟩ := hS
  intro ε hε hε'
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (eventually_split_big hA hc hc' hε)
  refine ⟨x₀, fun x hx d N r k hd hd4 hd100 hdN hN hlogN hk hr => ?_⟩
  obtain ⟨hx1, hE1, hE2⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set B := 3 + 9 * x ^ (ε / 5) * Real.log x ^ 2 with hB
  set K := (k : ℝ) * Real.exp (x ^ ε) with hK
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hKe : Real.exp (x ^ ε) ≤ K := le_mul_of_one_le_left (Real.exp_pos _).le hk1
  have hK1 : 1 ≤ K := (Real.one_le_exp (by positivity)).trans hKe
  have hK0 : 0 < K := by linarith
  have hlogK : x ^ ε ≤ Real.log K := by
    rw [hK, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    linarith [Real.log_nonneg hk1]
  have hlogY : Real.log (K ^ 8) = 8 * Real.log K := by rw [Real.log_pow]; norm_num
  have hY0 : 0 < Real.log (K ^ 8) := by rw [hlogY]; linarith [Real.rpow_pos_of_pos hx0 ε]
  -- `ShortNorm` at `Y = K^8`, `h = 1`, `M = N`
  have hNd : d ≤ N := Nat.le_of_dvd hN hdN
  have hN3 : 3 ≤ N := by omega
  have hdR : (d : ℝ) ≤ N := by exact_mod_cast hNd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hlog4 : Real.log (4 * d * N ^ 2) ≤ B := by
    have hl4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
    calc Real.log (4 * d * N ^ 2) ≤ Real.log (4 * N ^ 3) :=
          Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (N : ℝ)])
      _ = Real.log 4 + 3 * Real.log N := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 3 + 3 * (3 * x ^ (ε / 5) * Real.log x ^ 2) := by gcongr
      _ = B := by rw [hB]; ring
  have hsqrt : 2 * x ^ (ε / 2) ≤ √(Real.log (K ^ 8)) := by
    have hsq : (x ^ (ε / 2)) ^ 2 = x ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [Real.le_sqrt (by positivity) hY0.le, mul_pow, hsq, hlogY]
    linarith [Real.rpow_pos_of_pos hx0 ε]
  have hcount := H d N hd hd4 hd100 hN3 (K ^ 8) 1 (by nlinarith)
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))) le_rfl
  -- the count beats `(3r + 1)³K^6`
  have hr3 : (3 * r + 1 : ℝ) ^ 3 ≤ 1000 * x ^ 15 := by
    have h5 : x ^ (9 / 2 + 10 * ε) ≤ x ^ 5 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    have hx5 : 1 ≤ x ^ 5 := one_le_pow₀ hx1
    have h10 : (3 * r + 1 : ℝ) ≤ 10 * x ^ 5 := by linarith
    calc (3 * r + 1 : ℝ) ^ 3 ≤ (10 * x ^ 5) ^ 3 := pow_le_pow_left₀ (by positivity) h10 3
      _ = 1000 * x ^ 15 := by ring
  have hP : (4 * d * N ^ 2 : ℝ) ^ A ≤ Real.exp (A * B) := by
    rw [Real.rpow_def_of_pos (by positivity), mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog4 hA.le)
  have hLY : Real.log (K ^ 8) ≤ 8 * K := by
    rw [hlogY]; linarith [Real.log_le_sub_one_of_pos hK0]
  have hkey : (3 * r + 1 : ℝ) ^ 3 * K ^ 6 <
      c' * 1 * K ^ 8 / ((4 * d * N ^ 2 : ℝ) ^ A * Real.log (K ^ 8)) := by
    rw [lt_div_iff₀ (by positivity)]
    calc (3 * r + 1 : ℝ) ^ 3 * K ^ 6 * ((4 * d * N ^ 2 : ℝ) ^ A * Real.log (K ^ 8))
        ≤ 1000 * x ^ 15 * K ^ 6 * (Real.exp (A * B) * (8 * K)) := by gcongr
      _ = 8000 * x ^ 15 * Real.exp (A * B) * K ^ 7 := by ring
      _ < c' * Real.exp (x ^ ε) * K ^ 7 := by gcongr
      _ ≤ c' * K * K ^ 7 := by gcongr
      _ = c' * 1 * K ^ 8 := by ring
  -- two primes of the count with disjoint exceptional sets
  obtain ⟨g₀, hg₀, g₁, hg₁, hne, hdisj⟩ := exists_disjoint_excSet hK1 r
    (fun g hg => ⟨hg.2.2.1.two_le, hg.1, by linarith [hg.2.1]⟩) (hkey.trans_le hcount)
  refine ⟨g₀, g₁, hg₀.2.2.1, hg₁.2.2.1, hne, ?_, hdisj⟩
  intro g hg
  have hgG : K ^ 8 < g ∧ (g : ℝ) ≤ K ^ 8 * (1 + 1) ∧ g.Prime ∧ ∃ a b : ℤ, 4 * (g : ℤ) = a ^ 2 + d * b ^ 2 ∧
      (N : ℤ) ∣ b ∧ a ≡ b + 2 [ZMOD 2 * N] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hg₀
    · exact hg₁
  exact ⟨hgG.1.le, by linarith [hgG.2.1], hgG.2.2.2⟩

/-- **`(−d/g) = 1` for a prime of norm form** `4g = α² + dβ²` with `d ≥ 9` and `d ∣ β`: `g ∤ β`, since `g ∣ β`
gives `g ∣ α`, so `g² ∣ 4g` and `g = 2`, and then `8 = α² + dβ²` has no solution; hence `g ∤ d`, and
`−d ≡ (α/β)²` modulo `g`. -/
theorem jacobiSym_neg_d_of_norm {g d : ℕ} {α β : ℤ} (h : 4 * (g : ℤ) = α ^ 2 + d * β ^ 2) (hg : g.Prime)
    (hd : 9 ≤ d) (hdβ : (d : ℤ) ∣ β) : jacobiSym (-(d : ℤ)) g = 1 := by
  have hgZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.1 hg
  have hgβ : ¬ (g : ℤ) ∣ β := by
    intro hβ
    have hα : (g : ℤ) ∣ α := hgZ.dvd_of_dvd_pow (n := 2) ⟨4 - d * (β / g) ^ 2 * g, by
      obtain ⟨b, rfl⟩ := hβ
      rw [Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 hg.ne_zero)]
      linear_combination -h⟩
    obtain ⟨a, rfl⟩ := hα
    obtain ⟨b, rfl⟩ := hβ
    have h4 : (g : ℤ) ∣ 4 := ⟨a ^ 2 + d * b ^ 2, by
      have hg0 : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hg.ne_zero
      apply mul_left_cancel₀ hg0
      linear_combination h⟩
    have hg2 : g = 2 := by
      have h4' : g ∣ 2 ^ 2 := by exact_mod_cast h4
      exact (Nat.prime_dvd_prime_iff_eq hg Nat.prime_two).1 (hg.dvd_of_dvd_pow h4')
    subst hg2
    have hd9 : (9 : ℤ) ≤ d := by exact_mod_cast hd
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      have ha : a ^ 2 = 2 := by push_cast at h; nlinarith
      have h3 : -2 < a ∧ a < 2 := by constructor <;> nlinarith
      obtain ⟨h3a, h3b⟩ := h3
      interval_cases a <;> norm_num at ha
    · have hb1 : 1 ≤ b ^ 2 := by
        have := sq_nonneg b
        have : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
        omega
      push_cast at h
      nlinarith [sq_nonneg a]
  have hgd : ¬ (g : ℤ) ∣ d := fun h' => hgβ (h'.trans hdβ)
  have := Fact.mk hg
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hd0 : ((-(d : ℤ) : ℤ) : ZMod g) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_neg]
    exact hgd
  have hβ0 : ((β : ℤ) : ZMod g) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hgβ
  refine (legendreSym.eq_one_iff g hd0).2 ⟨(α : ZMod g) / β, ?_⟩
  have h' := congrArg (Int.cast : ℤ → ZMod g) h
  push_cast at h' ⊢
  rw [ZMod.natCast_self, mul_zero] at h'
  field_simp
  linear_combination h'

end ZetaBalance

#print axioms ZetaBalance.exists_split_primes
#print axioms ZetaBalance.jacobiSym_neg_d_of_norm
