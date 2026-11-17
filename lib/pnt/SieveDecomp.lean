/-
# Families of prime tuples, and Buchstab's identity at one `n`

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statements. An `Atom k` is one condition on a `k`-tuple `x` of primes: `b ≤ x_t`, `x_t < b`, `x_t < x_s`,
`∏_{i∈T} x_i ≤ b` or `b < ∏_{i∈T} x_i` (`Atom.sem`). The family `famSet k Y spec` is the set of `k`-tuples of primes
up to `Y` that satisfy every atom of `spec`. For weights `g` on `(N₁, N₂]`, `famI` sums the terms
`S_g(∏rt, rt_last) = Σ_n g(n)[∏rt ∣ n, no prime factor of n below rt_last]` over a family, and `famJ` the terms
`S_g(∏rt, z)`.

* `RTg_eq`: with positive thresholds, a family is `SieveChain.RTg` of its atoms' comparisons (`Atom.toG`);
  `Atom.toG_holds`: with a positive threshold, on entries at least `1`, the comparison holds exactly when the atom
  does, and `Atom.toG_c_le`: its part at `m = 0` is at most `|log thr|`.
* `buchstab_pt`: Buchstab's identity at one `n ≠ 0`. For `W` whose primes are at least `P ≥ z`,
  `[W ∣ n, rough P n] = [W ∣ n, rough z n] − Σ_{z ≤ p < P} [Wp ∣ n, rough p n]`; `dvd_rough_iff`: for a prime `p`
  and `n ≥ 2`, `p ∣ n` with `n` free of primes below `p` means `p = minFac n`.
* `famI_eq_zero`, `famI_vanish`: a family contributes `0` when no `n ∈ (N₁, N₂]` is counted, in particular when every
  `∏rt ≤ N₁` while `∏rt·rt_last > N₂`.

The file imports `SieveChain.lean`.
-/
import SieveChain

open Real Finset SieveFamily SieveChain

namespace SieveDecomp

open Classical

/-! ### Atoms of a family's region -/

/-- An atom of a family's region: a threshold for one prime, two primes compared, or a product of primes against a
threshold. -/
inductive Atom (k : ℕ) where
  | ge (t : Fin k) (b : ℝ)
  | lt (t : Fin k) (b : ℝ)
  | ltVar (s t : Fin k)
  | prodLe (T : Finset (Fin k)) (b : ℝ)
  | prodGt (T : Finset (Fin k)) (b : ℝ)

namespace Atom

variable {k : ℕ}

/-- What an atom says of a tuple: `b ≤ x_t`, `x_t < b`, `x_t < x_s`, `∏_T x ≤ b`, `b < ∏_T x`. -/
def sem : Atom k → (Fin k → ℕ) → Prop
  | ge t b, x => b ≤ x t
  | lt t b, x => (x t : ℝ) < b
  | ltVar s t, x => x t < x s
  | prodLe T b, x => ∏ i ∈ T, (x i : ℝ) ≤ b
  | prodGt T b, x => b < ∏ i ∈ T, (x i : ℝ)

@[simp] theorem sem_ge (t : Fin k) (b : ℝ) (x : Fin k → ℕ) : (ge t b).sem x ↔ b ≤ x t := Iff.rfl
@[simp] theorem sem_lt (t : Fin k) (b : ℝ) (x : Fin k → ℕ) : (lt t b).sem x ↔ (x t : ℝ) < b := Iff.rfl
@[simp] theorem sem_ltVar (s t : Fin k) (x : Fin k → ℕ) : (ltVar s t).sem x ↔ x t < x s := Iff.rfl
@[simp] theorem sem_prodLe (T : Finset (Fin k)) (b : ℝ) (x : Fin k → ℕ) :
    (prodLe T b).sem x ↔ ∏ i ∈ T, (x i : ℝ) ≤ b := Iff.rfl
@[simp] theorem sem_prodGt (T : Finset (Fin k)) (b : ℝ) (x : Fin k → ℕ) :
    (prodGt T b).sem x ↔ b < ∏ i ∈ T, (x i : ℝ) := Iff.rfl

/-- The atom's threshold (`1` for two primes compared). -/
noncomputable def thr : Atom k → ℝ
  | ge _ b => b
  | lt _ b => b
  | ltVar _ _ => 1
  | prodLe _ b => b
  | prodGt _ b => b

/-- The atom as a comparison. -/
noncomputable def toG : Atom k → GCmp k
  | ge t b => ⟨fun _ => -Real.log b, fun i => if i = t then 1 else 0, false, fun i => by split_ifs <;> simp⟩
  | lt t b => ⟨fun _ => Real.log b, fun i => -(if i = t then 1 else 0), true, fun i => by split_ifs <;> simp⟩
  | ltVar s t => ⟨fun _ => 0, fun i => (if i = s then 1 else 0) - (if i = t then 1 else 0), true,
      fun i => by split_ifs <;> simp⟩
  | prodLe T b => ⟨fun _ => Real.log b, fun i => -(if i ∈ T then 1 else 0), false,
      fun i => by split_ifs <;> simp⟩
  | prodGt T b => ⟨fun _ => -Real.log b, fun i => if i ∈ T then 1 else 0, true, fun i => by split_ifs <;> simp⟩

/-- With a positive threshold, on entries at least `1`, the comparison holds exactly when the atom does. -/
theorem toG_holds (A : Atom k) (hA : 0 < A.thr) (m : ℕ) {x : Fin k → ℕ} (hx : ∀ i, 1 ≤ x i) :
    A.toG.holds m x ↔ A.sem x := by
  have hpos : ∀ i, (0 : ℝ) < x i := fun i => by exact_mod_cast hx i
  have hprod : ∀ T : Finset (Fin k), (0 : ℝ) < ∏ i ∈ T, (x i : ℝ) := fun T => Finset.prod_pos fun i _ => hpos i
  cases A with
  | ge t b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, Bool.false_eq_true, ite_false, SieveCmp.sum_single,
      neg_add_eq_sub, sub_nonneg]
    exact Real.log_le_log_iff hA (hpos t)
  | lt t b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, ite_true, neg_mul, Finset.sum_neg_distrib, SieveCmp.sum_single,
      ← sub_eq_add_neg, sub_pos]
    exact Real.log_lt_log_iff (hpos t) hA
  | ltVar s t =>
    simp only [toG, GCmp.holds, GCmp.form, sem, ite_true, zero_add, sub_mul, Finset.sum_sub_distrib,
      SieveCmp.sum_single, sub_pos]
    rw [Real.log_lt_log_iff (hpos t) (hpos s), Nat.cast_lt]
  | prodLe T b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib,
      SieveCmp.sum_set T x hx, ← sub_eq_add_neg, sub_nonneg]
    exact Real.log_le_log_iff (hprod T) hA
  | prodGt T b =>
    simp only [thr] at hA
    simp only [toG, GCmp.holds, GCmp.form, sem, ite_true, SieveCmp.sum_set T x hx, neg_add_eq_sub, sub_pos]
    exact Real.log_lt_log_iff hA (hprod T)

/-- The comparison's part at `m = 0` is at most `|log thr|`. -/
theorem toG_c_le (A : Atom k) : A.toG.c 0 ≤ |Real.log A.thr| := by
  cases A <;> simp only [toG, thr, Real.log_one, abs_zero, le_refl] <;>
    first | exact neg_le_abs _ | exact le_abs_self _

end Atom

/-! ### Families -/

/-- The family of a list of atoms: the `k`-tuples of primes up to `Y` that satisfy them. -/
noncomputable def famSet (k Y : ℕ) (spec : List (Atom k)) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => SieveTypeIIU.primesLe Y).filter fun x => ∀ A ∈ spec, A.sem x

theorem mem_famSet {k Y : ℕ} {spec : List (Atom k)} {x : Fin k → ℕ} :
    x ∈ famSet k Y spec ↔ (∀ i, x i ≤ Y ∧ (x i).Prime) ∧ ∀ A ∈ spec, A.sem x := by
  rw [famSet, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [SieveTypeIIU.mem_primesLe]

/-- With positive thresholds, the family is `RTg` of the atoms' comparisons. -/
theorem RTg_eq (k Y : ℕ) (spec : List (Atom k)) (hpos : ∀ A ∈ spec, 0 < A.thr) :
    RTg k Y (spec.map Atom.toG) = famSet k Y spec := by
  unfold RTg famSet
  refine Finset.filter_congr fun x hx => ?_
  rw [Fintype.mem_piFinset] at hx
  have hx1 : ∀ i, 1 ≤ x i := fun i => (SieveTypeIIU.mem_primesLe.1 (hx i)).2.one_lt.le
  simp only [List.forall_mem_map]
  exact forall₂_congr fun A hA => A.toG_holds (hpos A hA) 0 hx1

/-- The terms `S(A_{∏rt}, rt_last)` of a family, with weights `g`. -/
noncomputable def famI (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) : ℝ :=
  ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, g n *
    (if (∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n then 1 else 0)

/-- The terms `S(A_{∏rt}, z)` of a family, with weights `g`. -/
noncomputable def famJ (g : ℕ → ℝ) (N₁ N₂ z : ℕ) {k : ℕ} (F : Finset (Fin k → ℕ)) : ℝ :=
  ∑ rt ∈ F, ∑ n ∈ Ioc N₁ N₂, g n * (if (∏ i, rt i) ∣ n ∧ SieveTree.rough z n then 1 else 0)

theorem famI_nonneg {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ)) :
    0 ≤ famI g N₁ N₂ F :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun n _ => mul_nonneg (hg n) (by split_ifs <;> norm_num)

/-! ### Buchstab's identity at one `n` -/

/-- For a prime `p` and `n ≥ 2`, `p ∣ n` with `n` free of primes below `p` means `p = minFac n`. -/
theorem dvd_rough_iff {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    p ∣ n ∧ SieveTree.rough p n ↔ p = Nat.minFac n := by
  constructor
  · rintro ⟨hd, hr⟩
    have h1 := Nat.minFac_le_of_dvd hp.two_le hd
    have h2 := (SieveStops2.rough_iff_le_minFac hn).1 hr
    omega
  · rintro rfl
    exact ⟨Nat.minFac_dvd n, (SieveStops2.rough_iff_le_minFac hn).2 le_rfl⟩

/-- **Buchstab's identity at one `n`.** For `W` whose primes are at least `P ≥ z` and `n ≠ 0`:
`[W ∣ n, rough P n] = [W ∣ n, rough z n] − Σ_{z ≤ p < P} [Wp ∣ n, rough p n]`. -/
theorem buchstab_pt {W P z n : ℕ} (hn : n ≠ 0) (hzP : z ≤ P) (hW : ∀ p : ℕ, p.Prime → p ∣ W → P ≤ p) :
    (if W ∣ n ∧ SieveTree.rough P n then (1 : ℝ) else 0) =
      (if W ∣ n ∧ SieveTree.rough z n then 1 else 0) -
        ∑ p ∈ SieveTree.primesIco z P, (if W * p ∣ n ∧ SieveTree.rough p n then 1 else 0) := by
  by_cases hWn : W ∣ n
  · have hcop : ∀ p ∈ SieveTree.primesIco z P, (W * p ∣ n ↔ p ∣ n) := by
      intro p hp
      rw [SieveTree.mem_primesIco] at hp
      have hc : Nat.Coprime W p := by
        refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.2.2).2 fun h => ?_)
        have := hW p hp.2.2 h
        omega
      exact ⟨fun h => dvd_trans (Dvd.intro_left W rfl) h, fun h => hc.mul_dvd_of_dvd_of_dvd hWn h⟩
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · -- `n = 1`: every condition is on primes dividing `1`
      have hn1 : n = 1 := by omega
      subst hn1
      have hr : ∀ w, SieveTree.rough w 1 := fun w p _ hp hd => hp.one_lt.ne' (Nat.dvd_one.1 hd)
      rw [Finset.sum_eq_zero]
      · simp [hWn, hr]
      intro p hp
      rw [ite_eq_right_iff]
      rintro ⟨hd, -⟩
      have := (SieveTree.mem_primesIco.1 hp).2.2
      exact (this.one_lt.ne' (Nat.dvd_one.1 (dvd_trans (Dvd.intro_left W rfl) hd))).elim
    · have hsum : ∑ p ∈ SieveTree.primesIco z P, (if W * p ∣ n ∧ SieveTree.rough p n then (1 : ℝ) else 0) =
          if z ≤ Nat.minFac n ∧ Nat.minFac n < P then 1 else 0 := by
        have hterm : ∀ p ∈ SieveTree.primesIco z P,
            (if W * p ∣ n ∧ SieveTree.rough p n then (1 : ℝ) else 0) = if p = Nat.minFac n then 1 else 0 := by
          intro p hp
          have hiff : (W * p ∣ n ∧ SieveTree.rough p n) ↔ p = Nat.minFac n := by
            rw [hcop p hp]; exact dvd_rough_iff (SieveTree.mem_primesIco.1 hp).2.2 h2
          simp only [hiff]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
        simp only [SieveTree.mem_primesIco, Nat.minFac_prime (by omega : n ≠ 1), and_true]
      rw [hsum]
      have e1 : SieveTree.rough P n ↔ P ≤ Nat.minFac n := SieveStops2.rough_iff_le_minFac h2
      have e2 : SieveTree.rough z n ↔ z ≤ Nat.minFac n := SieveStops2.rough_iff_le_minFac h2
      simp only [e1, e2]
      by_cases ha : P ≤ Nat.minFac n
      · have hb : z ≤ Nat.minFac n := le_trans hzP ha
        simp [hWn, ha, hb, not_lt.2 ha]
      · by_cases hb : z ≤ Nat.minFac n
        · simp [hWn, ha, hb, not_le.1 ha]
        · simp [hWn, ha, hb]
  · have h0 : ∀ p, ¬ (W * p ∣ n ∧ SieveTree.rough p n) := fun p h => hWn (dvd_trans (Dvd.intro _ rfl) h.1)
    simp [hWn, h0]

theorem prod_snoc {k : ℕ} (rt : Fin k → ℕ) (p : ℕ) : ∏ i, (Fin.snoc rt p : Fin (k + 1) → ℕ) i = (∏ i, rt i) * p := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-! ### Families that contribute `0` -/

/-- A family none of whose terms has an `n ∈ (N₁, N₂]` contributes `0`. -/
theorem famI_eq_zero (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ))
    (h : ∀ rt ∈ F, ∀ n ∈ Ioc N₁ N₂, ¬ ((∏ i, rt i) ∣ n ∧ SieveTree.rough (rt (Fin.last k')) n)) :
    famI g N₁ N₂ F = 0 :=
  Finset.sum_eq_zero fun rt hrt => Finset.sum_eq_zero fun n hn => by rw [ite_eq_right (h rt hrt n hn), mul_zero]

/-! ### Products at most `N₁` whose last prime takes them past `N₂` -/

/-- A family whose products are at most `N₁` and whose products times their last prime exceed `N₂` contributes `0`:
its `n = (∏rt)c ∈ (N₁, N₂]` would have `c ≥ 2` with no prime factor below `rt_last`. -/
theorem famI_vanish (g : ℕ → ℝ) (N₁ N₂ : ℕ) {k' : ℕ} (F : Finset (Fin (k' + 1) → ℕ))
    (h : ∀ rt ∈ F, (∏ i, rt i) ≤ N₁ ∧ N₂ < (∏ i, rt i) * rt (Fin.last k')) :
    famI g N₁ N₂ F = 0 := by
  refine famI_eq_zero g N₁ N₂ F fun rt hrt m hm hdr => ?_
  obtain ⟨hW, hN⟩ := h rt hrt
  obtain ⟨⟨c, rfl⟩, hr⟩ := hdr
  rw [Finset.mem_Ioc] at hm
  set W := ∏ i, rt i with hWdef
  have hc2 : 2 ≤ c := by
    by_contra hlt
    have h1 : W * c ≤ W * 1 := Nat.mul_le_mul_left W (by omega)
    omega
  have hrc : SieveTree.rough (rt (Fin.last k')) c := fun p hp1 hpp hpc => hr p hp1 hpp (dvd_mul_of_dvd_right hpc W)
  have hmin := (SieveStops2.rough_iff_le_minFac hc2).1 hrc
  have hmc := Nat.minFac_le (by omega : 0 < c)
  have : W * rt (Fin.last k') ≤ W * c := Nat.mul_le_mul_left W (by omega)
  omega

end SieveDecomp
