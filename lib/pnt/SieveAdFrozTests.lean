/-
# The tests of the tree over the frozen part of a reversal are sound

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. `SieveAdFrozDefs.lean` has the tests `SieveAd.frozTests` of the tree over the frozen part
`SieveAd.frozS`, on the bits of the search's lists. Here they are sound in the sense of `SieveAd.SoundF`: a test
that passes a box `ch ++ β` evaluates the term of the chain `ch` over the frozen part, or its terms at the floor.

* `loR_eq`, `hiR_eq`, `hiRc_eq`: the exponents that the tests read are those of the role sets
  (`SieveAd.loRole`, `SieveAd.hiRole`) of the bits: the chain's primes at the low bits, the primes of `β` at the
  next, and the cofactor at the bit after them.
* `frozTests_sound`: **the tests are sound for the frozen part**, for `e₁ ≤ e₂ ≤ DEN`, `(T + 1)·lo_s ≥ DEN + 1`
  and `Kb ≥ 12 + T`; `frozTests_sound_at` with the route and its exponent as variables.

The file imports `SieveAdFrozI.lean` and `SieveAdFrozDefs.lean`.
-/
import SieveAdFrozI
import SieveAdFrozDefs

open Real Finset Filter SieveDecomp SieveLeaves SieveQ SieveRough SieveRoute

namespace SieveAd

open Classical
open SieveCert (DEN DEN_pos')

/-- The sum of the lower ends over the complement of a set is the whole sum minus the set's. -/
theorem sum_mset_compl_lo (bl : List Cell) (k : ℕ) (h : bl.length = k) (m : ℕ) :
    ∑ i ∈ (mset k m)ᶜ, (boxFn bl k h i).1 = loSum bl - mSum (fun c => c.1) bl m := by
  have h1 := Finset.sum_add_sum_compl (mset k m) fun i => (boxFn bl k h i).1
  rw [sum_mset (fun c => c.1) bl k h m, sum_boxFn (fun c => c.1) bl k h, ← loSum_eq] at h1
  omega

/-- Numbers with no common bit have none after a shift. -/
theorem land_div_two_pow {a b : ℕ} (h : a &&& b = 0) (k : ℕ) : (a / 2 ^ k) &&& (b / 2 ^ k) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit, ← Nat.testBit_and, h,
    Nat.zero_testBit]

/-- The lower exponent that the tests read is that of the role set of the bits. -/
theorem loR_eq (e₁ : ℕ) (β ch : List Cell) {s k : ℕ} (hβ : β.length = s + 1) (hk : ch.length = k) (m : ℕ) :
    loR e₁ β ch m = loRole (boxFn β (s + 1) hβ) (boxFn ch k hk) e₁ (mset (s + 1) (m / 2 ^ k))
      (Nat.testBit (m / 2 ^ k) (s + 1)) (mset k m) := by
  unfold loR loRole
  rw [sum_mset (fun c => c.1) β (s + 1) hβ, sum_mset_compl β (s + 1) hβ, sum_mset (fun c => c.1) ch k hk, hβ, hk]

/-- The upper exponent that the tests read is that of the role set of the bits. -/
theorem hiR_eq (e₂ : ℕ) (β ch : List Cell) {s k : ℕ} (hβ : β.length = s + 1) (hk : ch.length = k) (m : ℕ) :
    hiR e₂ β ch m = hiRole (boxFn β (s + 1) hβ) (boxFn ch k hk) e₂ (mset (s + 1) (m / 2 ^ k))
      (Nat.testBit (m / 2 ^ k) (s + 1)) (mset k m) := by
  unfold hiR hiRole
  rw [sum_mset (fun c => c.2) β (s + 1) hβ, sum_mset_compl_lo β (s + 1) hβ, sum_mset (fun c => c.2) ch k hk, hβ,
    hk]

/-- The upper exponent that the tests read for the complement is that of the role set of the other parts. -/
theorem hiRc_eq (e₂ : ℕ) (β ch : List Cell) {s k : ℕ} (hβ : β.length = s + 1) (hk : ch.length = k) (m : ℕ) :
    hiRc e₂ β ch m = hiRole (boxFn β (s + 1) hβ) (boxFn ch k hk) e₂ (mset (s + 1) (m / 2 ^ k))ᶜ
      (!Nat.testBit (m / 2 ^ k) (s + 1)) (mset k m)ᶜ := by
  unfold hiRc hiRole
  rw [compl_compl, sum_mset (fun c => c.1) β (s + 1) hβ, sum_mset_compl β (s + 1) hβ, sum_mset_compl ch k hk, hβ,
    hk]
  cases Nat.testBit (m / 2 ^ k) (s + 1) <;> rfl

variable [Route] [RouteOK] [SieveCert.IBPar] [IBFits]

/-- **The tests of the tree over the frozen part are sound.** For a list `β` of `s + 1` cells, `e₁ ≤ e₂ ≤ DEN`,
`(T + 1)·lo_s ≥ DEN + 1` for the lower end `lo_s` of the cell of the least prime of `β`, and `Kb ≥ 12 + T`: on a
box `ch ++ β` of at most twelve cells, a test of `frozTests e₁ e₂ Kb β` that passes evaluates the term of the
chain `ch` over the frozen part `frozS` of `β` and the slab, or its terms at the floor. -/
theorem frozTests_sound {e₁ e₂ s : ℕ} (β : List Cell) (hβ : β.length = s + 1) (he : e₁ ≤ e₂) (he₂ : e₂ ≤ DEN)
    {T Kb : ℕ} (hT : DEN + 1 ≤ (T + 1) * (boxFn β (s + 1) hβ (Fin.last s)).1) (hKb : 12 + T ≤ Kb) :
    SoundF (frozTests e₁ e₂ Kb β) (fun q => frozS q e₁ e₂ (boxFn β (s + 1) hβ)) frozR β := by
  have he₁ : e₁ ≤ DEN := he.trans he₂
  refine ⟨fun ch cfg k' h hlen hok => ?_, fun ch f cfg k h hlen hok => ?_⟩
  · have hok' : okIF e₁ e₂ β (ch ++ β) cfg = true := hok
    unfold okIF at hok'
    rw [chainOf_append] at hok'
    simp only [Bool.and_eq_true, Nat.blt_eq] at hok'
    obtain ⟨⟨⟨hcells, hland⟩, hρ⟩, hcore⟩ := hok'
    have hland' : cfg.s0 &&& cfg.sr = 0 := Nat.eq_of_beq_eq_true hland
    have hc := (cellsFrom_iff 1 (ch ++ β)).1 hcells
    rw [loR_eq e₁ β ch hβ h] at hρ
    rw [loR_eq e₁ β ch hβ h cfg.s0, hiR_eq e₂ β ch hβ h cfg.s0, loR_eq e₁ β ch hβ h cfg.sr,
      hiR_eq e₂ β ch hβ h cfg.sr] at hcore
    have hmy : (Nat.testBit (cfg.s0 / 2 ^ (k' + 1)) (s + 1) && Nat.testBit (cfg.sr / 2 ^ (k' + 1)) (s + 1)) =
        false := by
      rw [← Nat.testBit_and, land_div_two_pow hland', Nat.zero_testBit]
    exact evIF_froz_two (fun i => hc _ (List.mem_append_right _ (boxFn_mem β _ hβ i))) he he₂
      (fun j => hc _ (List.mem_append_left _ (boxFn_mem ch _ h j))) _ _ _ _ _ _
      (mset_disjoint (s + 1) (land_div_two_pow hland' (k' + 1))) hmy (mset_disjoint (k' + 1) hland') hρ hcore
  · have hok' : cond (Nat.beq cfg.kind 2) (okJF3 e₁ e₂ Kb β (ch ++ β) f cfg)
        (okJF2 e₁ e₂ Kb β (ch ++ β) f cfg) = true := hok
    rw [h, hβ] at hlen
    have hKb' : s + 1 + T + k ≤ Kb := by omega
    cases hk2 : Nat.beq cfg.kind 2
    · rw [hk2] at hok'
      have hok2 : okJF2 e₁ e₂ Kb β (ch ++ β) f cfg = true := hok'
      unfold okJF2 at hok2
      rw [chainOf_append] at hok2
      simp only [Bool.and_eq_true, Nat.blt_eq] at hok2
      obtain ⟨⟨⟨⟨hf, hcells⟩, hland⟩, hρ⟩, hcore⟩ := hok2
      have hland' : cfg.s0 &&& cfg.sr = 0 := Nat.eq_of_beq_eq_true hland
      have hc := (cellsFrom_iff f (ch ++ β)).1 hcells
      have hβc : ∀ i, f ≤ (boxFn β (s + 1) hβ i).1 ∧ (boxFn β (s + 1) hβ i).1 ≤ DEN ∧
          (boxFn β (s + 1) hβ i).2 ≤ DEN := fun i => by
        have := hc _ (List.mem_append_right _ (boxFn_mem β _ hβ i))
        exact ⟨this.1, this.2.1.trans this.2.2, this.2.2⟩
      have hbc : ∀ j, f ≤ (boxFn ch k h j).1 ∧ (boxFn ch k h j).1 ≤ DEN ∧ (boxFn ch k h j).2 ≤ DEN := fun j => by
        have := hc _ (List.mem_append_left _ (boxFn_mem ch _ h j))
        exact ⟨this.1, this.2.1.trans this.2.2, this.2.2⟩
      have hfD : f ≤ DEN := (hβc (Fin.last s)).1.trans (hβc (Fin.last s)).2.1
      rw [loR_eq e₁ β ch hβ h] at hρ
      rw [loR_eq e₁ β ch hβ h cfg.sr, hiR_eq e₂ β ch hβ h cfg.sr, loR_eq e₁ β ch hβ h cfg.s0,
        hiR_eq e₂ β ch hβ h cfg.s0, hiR_eq e₂ β ch hβ h cfg.s1, hiRc_eq e₂ β ch hβ h cfg.s1] at hcore
      have hmy : (Nat.testBit (cfg.s0 / 2 ^ k) (s + 1) && Nat.testBit (cfg.sr / 2 ^ k) (s + 1)) = false := by
        rw [← Nat.testBit_and, land_div_two_pow hland', Nat.zero_testBit]
      exact evJF_froz_two hf hfD hβc he₁ he₂ hT hbc _ _ _ _ _ _ _ _ _
        (mset_disjoint (s + 1) (land_div_two_pow hland' k)) hmy (mset_disjoint k hland') cfg.e _ _ _ Kb hKb' hρ
        hcore
    · rw [hk2] at hok'
      have hok3 : okJF3 e₁ e₂ Kb β (ch ++ β) f cfg = true := hok'
      unfold okJF3 at hok3
      rw [chainOf_append] at hok3
      simp only [Bool.and_eq_true, Nat.blt_eq] at hok3
      obtain ⟨⟨hf, hcells⟩, hcore⟩ := hok3
      have hc := (cellsFrom_iff f (ch ++ β)).1 hcells
      have hβc : ∀ i, f ≤ (boxFn β (s + 1) hβ i).1 ∧ (boxFn β (s + 1) hβ i).1 ≤ DEN ∧
          (boxFn β (s + 1) hβ i).2 ≤ DEN := fun i => by
        have := hc _ (List.mem_append_right _ (boxFn_mem β _ hβ i))
        exact ⟨this.1, this.2.1.trans this.2.2, this.2.2⟩
      have hbc : ∀ j, f ≤ (boxFn ch k h j).1 ∧ (boxFn ch k h j).1 ≤ DEN ∧ (boxFn ch k h j).2 ≤ DEN := fun j => by
        have := hc _ (List.mem_append_left _ (boxFn_mem ch _ h j))
        exact ⟨this.1, this.2.1.trans this.2.2, this.2.2⟩
      have hfD : f ≤ DEN := (hβc (Fin.last s)).1.trans (hβc (Fin.last s)).2.1
      rw [loR_eq e₁ β ch hβ h cfg.s0, hiR_eq e₂ β ch hβ h cfg.s0, hiR_eq e₂ β ch hβ h cfg.s1,
        hiRc_eq e₂ β ch hβ h cfg.s1] at hcore
      exact evJF_froz_fill hf hfD hβc he₁ he₂ hT hbc _ _ _ _ _ _ cfg.e _ _ _ _ _ Kb hKb' hcore

omit [Route] [RouteOK] [SieveCert.IBPar] [IBFits] in
/-- **The tests of the tree over the frozen part are sound, for any route**: `frozTests_sound` with the route and
its exponent as variables. -/
theorem frozTests_sound_at (Rt : Route) (hRt : @RouteOK Rt) (Pr : SieveCert.IBPar) (hPr : @IBFits Rt Pr)
    {e₁ e₂ s : ℕ} (β : List Cell) (hβ : β.length = s + 1) (he : e₁ ≤ e₂) (he₂ : e₂ ≤ DEN) {T Kb : ℕ}
    (hT : DEN + 1 ≤ (T + 1) * (boxFn β (s + 1) hβ (Fin.last s)).1) (hKb : 12 + T ≤ Kb) :
    @SoundF Rt (@frozTests Pr e₁ e₂ Kb β) _ (fun q => @frozS Rt q e₁ e₂ s (boxFn β (s + 1) hβ)) frozR β :=
  @frozTests_sound Rt hRt Pr hPr e₁ e₂ s β hβ he he₂ T Kb hT hKb

end SieveAd

#print axioms SieveAd.frozTests_sound_at
