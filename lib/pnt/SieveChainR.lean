/-
# Type II for chains with part of their product in the reflection of the window

Plain statements. `RTg`, `GCmp`, `merge` and `eS` are `SieveChain`'s; `rough z n` is `SieveTree`'s. `L`, `w₁` and `w₂`
are a route's parameters (`SieveRoute.Route`) with `RouteOK`, and the bound assumes its Type II estimate
(`hII : SieveRoute.TypeIIAt`). `N₁ = ⌊q^L⌋` and `N₂ = ⌊2q^L⌋`.

* `bigF z m`, `rank F x`, `readAt F i`: the prime factors of `m` at least `z`; the number of elements of `F` above `x`;
  the element of `F` of rank `i` (or `0`). `rank_readAt`, `readAt_rank`: on `F`, rank and reading are inverse.
* `card_bigF_lt`: for `z ≥ 2` and `1 ≤ m ≤ Y < z^B`, `m` has fewer than `B` prime factors at least `z`.
* `sum_slices`: **slices.** For `z ≥ 2` and `Y < z^B`, the pairs `(a, k)` of a strictly decreasing `s`-tuple `a` of
  primes at least `z` and an integer `k ≥ 1` with `∏a·k ≤ Y` are the pairs `(ι, m)` of a strictly increasing tuple of
  ranks below `B` (a *slice*, `slices s B`) and an `m ∈ [1, Y]` with that many prime factors at least `z` (`valid`),
  through `m = ∏a·k`, `a = readP z ι m` (`m`'s primes at least `z` read at the ranks `ι`) and `k = m/∏a`.
* `sum_pi_merge`: a sum over tuples on `Fin k` is a sum over their parts on `S` and on `Sᶜ`.
* `splitR`, `splitR_holds`: a comparison of the chain at `m`, as one of its part on `S` with the part on `Sᶜ` read from
  `m`.
* `chainTR_bound`: **chains with part of their product in the reflection.** Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`.
  There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit `a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of
  primes up to `N₂` that satisfy at most `J₀` comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such
  tuple strictly decreasing, with entries at least `q^{e₀}` and `W₀ < ∏_{i∈U} rt_i ≤ W₁` for a set `U` of indices,
  where `W₁ ≤ N₁`, `q^{w₁L} ≤ ⌊N₁/W₁⌋` and `⌊N₂/(W₀ + 1)⌋ ≤ q^{w₂L}`. Then the multiples `n ∈ (N₁, N₂]` of `∏rt` with no
  prime factor below `rt`'s last entry, summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`.

`SieveChain.chainTU_bound` is the case `U` of all indices. The Type II variable is `m = n/∏_{i∈U} rt_i`, in the window:
the primes off `U` and the rough rest of `n`. They are read back from `m` by their ranks among `m`'s primes at least
`q^{e₀}`, one slice at a time, and the slices are boundedly many.

The proof of `chainTR_bound`: `SieveChain.sum_mult_eq` writes the multiples as `∏rt·k` with `k` rough; `sum_pi_merge`
splits `rt` into its parts on `U` and off `U`, and `sum_slices` turns the part off `U` and `k` into a slice and `m`. For
each slice, `splitR` turns the comparisons `Ω` and the roughness of `k` into comparisons of the part on `U` with
`m`-parts read from `m`, and `SieveChain.typeII_gcmp'` bounds the sum over `m` in `(⌊N₁/W₁⌋, ⌊N₂/(W₀ + 1)⌋]`.

The file imports `SieveChain.lean`.
-/
import SieveChain

open Real Finset SieveFamily SieveTree SieveRoute SieveChain

namespace SieveChainR

/-! ### Reading primes by their ranks -/

/-- The prime factors of `m` at least `z`. -/
noncomputable def bigF (z m : ℕ) : Finset ℕ := m.primeFactors.filter (z ≤ ·)

/-- The rank of `x` in `F`, counted from the top: the number of elements of `F` above `x`. -/
def rank (F : Finset ℕ) (x : ℕ) : ℕ := (F.filter (x < ·)).card

/-- The element of `F` of rank `i`, counted from the top, or `0`. -/
noncomputable def readAt (F : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < F.card then SieveStops2.desc F.card F ⟨i, h⟩ else 0

theorem rank_desc {c : ℕ} {F : Finset ℕ} (h : F.card = c) (u : Fin c) : rank F (SieveStops2.desc c F u) = u := by
  have himg := SieveStops2.image_desc h
  have hanti := SieveStops2.desc_strictAnti h
  generalize SieveStops2.desc c F = d at himg hanti ⊢
  subst himg
  unfold rank
  rw [Finset.filter_image, Finset.card_image_of_injective _ hanti.injective]
  have e : (Finset.univ.filter fun v => d u < d v) = Finset.univ.filter fun v : Fin c => (v : ℕ) < u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hanti.lt_iff_gt, Fin.lt_def]
  rw [e, Fin.card_filter_val_lt]
  exact min_eq_right u.isLt.le

theorem readAt_of_lt {F : Finset ℕ} {i : ℕ} (h : i < F.card) :
    readAt F i = SieveStops2.desc F.card F ⟨i, h⟩ := by
  simp [readAt, h]

theorem readAt_mem {F : Finset ℕ} {i : ℕ} (h : i < F.card) : readAt F i ∈ F := by
  rw [readAt_of_lt h]
  exact SieveStops2.desc_mem rfl _

theorem rank_readAt {F : Finset ℕ} {i : ℕ} (h : i < F.card) : rank F (readAt F i) = i := by
  rw [readAt_of_lt h, rank_desc rfl]

theorem rank_lt_card {F : Finset ℕ} {x : ℕ} (hx : x ∈ F) : rank F x < F.card := by
  unfold rank
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := (Finset.mem_filter.1 (h hx)).2
  exact lt_irrefl _ this

theorem readAt_rank {F : Finset ℕ} {x : ℕ} (hx : x ∈ F) : readAt F (rank F x) = x := by
  have himg := SieveStops2.image_desc (rfl : F.card = F.card)
  rw [← himg] at hx
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
  rw [rank_desc rfl, readAt_of_lt u.isLt]

theorem readAt_lt {F : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < F.card) : readAt F j < readAt F i := by
  rw [readAt_of_lt hj, readAt_of_lt (lt_trans hij hj)]
  exact SieveStops2.desc_strictAnti rfl (Fin.mk_lt_mk.2 hij)

theorem rank_lt_rank {F : Finset ℕ} {x y : ℕ} (hy : y ∈ F) (hxy : x < y) : rank F y < rank F x := by
  unfold rank
  refine Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩
  · obtain ⟨htF, hyt⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_filter.2 ⟨htF, lt_trans hxy hyt⟩
  · have := (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hy, hxy⟩))).2
    exact lt_irrefl _ this

theorem mem_bigF {z m p : ℕ} : p ∈ bigF z m ↔ p.Prime ∧ p ∣ m ∧ m ≠ 0 ∧ z ≤ p := by
  rw [bigF, Finset.mem_filter, Nat.mem_primeFactors]
  tauto

/-- For `z ≥ 2` and `1 ≤ m ≤ Y < z^B`, `m` has fewer than `B` prime factors at least `z`. -/
theorem card_bigF_lt {z m Y B : ℕ} (hz : 2 ≤ z) (hm : 1 ≤ m) (hmY : m ≤ Y) (hB : Y < z ^ B) :
    (bigF z m).card < B := by
  have h1 : z ^ (bigF z m).card ≤ ∏ p ∈ bigF z m, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (mem_bigF.1 hp).2.2.2
  have h2 : ∏ p ∈ bigF z m, p ≤ ∏ p ∈ m.primeFactors, p :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) fun p hp _ =>
      (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have h3 : ∏ p ∈ m.primeFactors, p ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have h4 : z ^ (bigF z m).card < z ^ B := by omega
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 h4

/-! ### Slices -/

/-- The slices: strictly increasing `s`-tuples of ranks below `B`. -/
noncomputable def slices (s B : ℕ) : Finset (Fin s → ℕ) :=
  (Fintype.piFinset fun _ : Fin s => Finset.range B).filter StrictMono

/-- `m`'s primes at least `z`, read at the ranks `ι`. -/
noncomputable def readP {s : ℕ} (z : ℕ) (ι : Fin s → ℕ) (m : ℕ) : Fin s → ℕ := fun v => readAt (bigF z m) (ι v)

/-- The ranks `ι` read primes of `m`: each is below the number of `m`'s prime factors at least `z`. -/
def valid {s : ℕ} (z : ℕ) (ι : Fin s → ℕ) (m : ℕ) : Prop := ∀ v, ι v < (bigF z m).card

theorem card_slices_le (s B : ℕ) : (slices s B).card ≤ B ^ s := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]
  simp

theorem readP_mem {s z : ℕ} {ι : Fin s → ℕ} {m : ℕ} (h : valid z ι m) (v : Fin s) : readP z ι m v ∈ bigF z m :=
  readAt_mem (h v)

theorem readP_strictAnti {s z : ℕ} {ι : Fin s → ℕ} (hι : StrictMono ι) {m : ℕ} (h : valid z ι m) :
    StrictAnti (readP z ι m) := fun _ _ hvw => readAt_lt (hι hvw) (h _)

/-- The primes read at a valid slice divide `m`, together. -/
theorem prod_readP_dvd {s z : ℕ} {ι : Fin s → ℕ} (hι : StrictMono ι) {m : ℕ} (h : valid z ι m) :
    ∏ v, readP z ι m v ∣ m := by
  have hinj := (readP_strictAnti hι h).injective
  have e : ∏ v, readP z ι m v = ∏ p ∈ Finset.univ.image (readP z ι m), p :=
    (Finset.prod_image (f := fun p => p) fun v _ w _ hvw => hinj hvw).symm
  rw [e]
  refine dvd_trans (Finset.prod_dvd_prod_of_subset _ m.primeFactors (fun p => p) ?_) (Nat.prod_primeFactors_dvd m)
  intro p hp
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
  exact Finset.mem_of_mem_filter _ (readP_mem h v)

open Classical in
/-- **Slices.** For `z ≥ 2` and `Y < z^B`: the pairs `(a, k)` of a strictly decreasing tuple of primes at least `z` and
`k ≥ 1` with `∏a·k ≤ Y` are the pairs `(ι, m)` of a slice and a valid `m ∈ [1, Y]`, through `m = ∏a·k`,
`a = readP z ι m` and `k = m/∏a`. -/
theorem sum_slices {M : Type*} [AddCommMonoid M] {s z B Y : ℕ} (hz : 2 ≤ z) (hB : Y < z ^ B)
    (G : (Fin s → ℕ) → ℕ → M) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin s => SieveTypeIIU.primesLe Y), ∑ k ∈ Finset.Icc 1 Y,
        (if StrictAnti a ∧ (∀ v, z ≤ a v) ∧ (∏ v, a v) * k ≤ Y then G a k else 0) =
      ∑ ι ∈ slices s B, ∑ m ∈ Finset.Icc 1 Y,
        (if valid z ι m then G (readP z ι m) (m / ∏ v, readP z ι m v) else 0) := by
  rw [← Finset.sum_product' (f := fun a k => if StrictAnti a ∧ (∀ v, z ≤ a v) ∧ (∏ v, a v) * k ≤ Y then G a k
    else 0), ← Finset.sum_product' (f := fun ι m => if valid z ι m then
    G (readP z ι m) (m / ∏ v, readP z ι m v) else 0), ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun p => (fun v => rank (bigF z ((∏ v, p.1 v) * p.2)) (p.1 v), (∏ v, p.1 v) * p.2))
    (fun p => (readP z p.1 p.2, p.2 / ∏ v, readP z p.1 p.2 v)) ?_ ?_ ?_ ?_ ?_
  · -- into the slices
    rintro ⟨a, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc] at hp
    obtain ⟨⟨ha, hk1, -⟩, hsa, hz', hY⟩ := hp
    have hap : ∀ v, (a v).Prime := fun v => (SieveTypeIIU.mem_primesLe.1 (ha v)).2
    set m := (∏ v, a v) * k with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
      (Finset.prod_ne_zero_iff.2 fun v _ => (hap v).ne_zero) (by omega))
    have hmem : ∀ v, a v ∈ bigF z m := fun v => mem_bigF.2 ⟨hap v,
      dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ v)) (dvd_mul_right _ _), by omega, hz' v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, slices, Fintype.mem_piFinset,
      Finset.mem_range]
    refine ⟨⟨⟨fun v => lt_trans (rank_lt_card (hmem v)) (card_bigF_lt hz hm1 hY hB), fun v w hvw =>
      rank_lt_rank (hmem v) (hsa hvw)⟩, hm1, hY⟩, fun v => rank_lt_card (hmem v)⟩
  · -- back to the pairs
    rintro ⟨ι, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, slices, Fintype.mem_piFinset,
      Finset.mem_range] at hp
    obtain ⟨⟨⟨-, hι⟩, hm1, hmY⟩, hv⟩ := hp
    have hdvd := prod_readP_dvd hι hv
    have hmem := readP_mem hv
    have hprod0 : 0 < ∏ v, readP z ι m v := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hmul : (∏ v, readP z ι m v) * (m / ∏ v, readP z ι m v) = m := Nat.mul_div_cancel' hdvd
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]
    refine ⟨⟨fun v => ?_, ?_, ?_⟩, readP_strictAnti hι hv, fun v => (mem_bigF.1 (hmem v)).2.2.2,
      by rw [hmul]; exact hmY⟩
    · obtain ⟨hp, hpm, -, -⟩ := mem_bigF.1 (hmem v)
      exact SieveTypeIIU.mem_primesLe.2 ⟨le_trans (Nat.le_of_dvd (by omega) hpm) hmY, hp⟩
    · rcases Nat.eq_zero_or_pos (m / ∏ v, readP z ι m v) with h | h
      · rw [h, mul_zero] at hmul
        omega
      · exact h
    · exact le_trans (Nat.div_le_self _ _) hmY
  · -- left inverse
    rintro ⟨a, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc] at hp
    obtain ⟨⟨ha, hk1, -⟩, hsa, hz', hY⟩ := hp
    have hap : ∀ v, (a v).Prime := fun v => (SieveTypeIIU.mem_primesLe.1 (ha v)).2
    have hprod0 : 0 < ∏ v, a v := Finset.prod_pos fun v _ => (hap v).pos
    have hmem : ∀ v, a v ∈ bigF z ((∏ v, a v) * k) := fun v => mem_bigF.2 ⟨hap v,
      dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ v)) (dvd_mul_right _ _),
      Nat.mul_ne_zero hprod0.ne' (by omega), hz' v⟩
    have hread : readP z (fun v => rank (bigF z ((∏ v, a v) * k)) (a v)) ((∏ v, a v) * k) = a := by
      funext v
      exact readAt_rank (hmem v)
    simp only [Prod.mk.injEq]
    refine ⟨hread, ?_⟩
    rw [hread, Nat.mul_div_cancel_left _ hprod0]
  · -- right inverse
    rintro ⟨ι, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, slices, Fintype.mem_piFinset,
      Finset.mem_range] at hp
    obtain ⟨⟨⟨-, hι⟩, -, -⟩, hv⟩ := hp
    have hmul : (∏ v, readP z ι m v) * (m / ∏ v, readP z ι m v) = m := Nat.mul_div_cancel' (prod_readP_dvd hι hv)
    simp only [Prod.mk.injEq]
    refine ⟨?_, hmul⟩
    funext v
    rw [hmul]
    exact rank_readAt (hv v)
  · -- the summands
    rintro ⟨a, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc] at hp
    obtain ⟨⟨ha, hk1, -⟩, hsa, hz', hY⟩ := hp
    have hap : ∀ v, (a v).Prime := fun v => (SieveTypeIIU.mem_primesLe.1 (ha v)).2
    have hprod0 : 0 < ∏ v, a v := Finset.prod_pos fun v _ => (hap v).pos
    have hmem : ∀ v, a v ∈ bigF z ((∏ v, a v) * k) := fun v => mem_bigF.2 ⟨hap v,
      dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ v)) (dvd_mul_right _ _),
      Nat.mul_ne_zero hprod0.ne' (by omega), hz' v⟩
    have hread : readP z (fun v => rank (bigF z ((∏ v, a v) * k)) (a v)) ((∏ v, a v) * k) = a := by
      funext v
      exact readAt_rank (hmem v)
    simp only
    rw [hread, Nat.mul_div_cancel_left _ hprod0]

/-! ### Splitting a chain by a set of its indices -/

theorem eS_inr_strictMono {k : ℕ} {S : Finset (Fin k)} : StrictMono (fun v : Fin Sᶜ.card => eS S (Sum.inr v)) := by
  have e : (fun v : Fin Sᶜ.card => eS S (Sum.inr v)) = Sᶜ.orderEmbOfFin rfl := by
    funext v
    exact finSumEquivOfFinset_inr rfl rfl v
  rw [e]
  exact (Sᶜ.orderEmbOfFin rfl).strictMono

/-- A sum over tuples on `Fin k` is a sum over their parts on `S` and on `Sᶜ`. -/
theorem sum_pi_merge {M : Type*} [AddCommMonoid M] {k : ℕ} (S : Finset (Fin k)) (A : Finset ℕ)
    (f : (Fin k → ℕ) → M) :
    ∑ rt ∈ Fintype.piFinset (fun _ : Fin k => A), f rt =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin S.card => A), ∑ b ∈ Fintype.piFinset (fun _ : Fin Sᶜ.card => A),
        f (merge S x b) := by
  rw [← Finset.sum_product' (f := fun x b => f (merge S x b))]
  refine Finset.sum_nbij' (fun rt => (fun u => rt (eS S (Sum.inl u)), fun v => rt (eS S (Sum.inr v))))
    (fun p => merge S p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro rt hrt
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hrt ⊢
    exact ⟨fun u => hrt _, fun v => hrt _⟩
  · rintro ⟨x, b⟩ hp
    simp only [Finset.mem_product, Fintype.mem_piFinset] at hp ⊢
    intro i
    obtain ⟨y, rfl⟩ := (eS S).surjective i
    rcases y with u | v
    · rw [merge_inl]; exact hp.1 u
    · rw [merge_inr]; exact hp.2 v
  · intro rt _
    exact merge_split rt
  · rintro ⟨x, b⟩ _
    simp only [merge_inl, merge_inr]
  · intro rt _
    simp only [merge_split]

/-- A comparison of the chain at `m`, as one of its part on `S`, with the part on `Sᶜ` read from `m` by `rd`. -/
noncomputable def splitR {k : ℕ} (S : Finset (Fin k)) (rd : ℕ → Fin Sᶜ.card → ℕ) (C : GCmp k) : GCmp S.card where
  c := fun m => C.c m + ∑ v, C.e (eS S (Sum.inr v)) * Real.log (rd m v)
  e := fun u => C.e (eS S (Sum.inl u))
  strict := C.strict
  he := fun _ => C.he _

theorem splitR_form {k : ℕ} (S : Finset (Fin k)) (rd : ℕ → Fin Sᶜ.card → ℕ) (C : GCmp k) (m : ℕ)
    (x : Fin S.card → ℕ) : (splitR S rd C).form m x = C.form m (merge S x (rd m)) := by
  unfold GCmp.form splitR
  rw [sum_split (S := S) (fun i => C.e i * Real.log (merge S x (rd m) i))]
  simp only [merge_inl, merge_inr]
  ring

theorem splitR_holds {k : ℕ} (S : Finset (Fin k)) (rd : ℕ → Fin Sᶜ.card → ℕ) (C : GCmp k) (m : ℕ)
    (x : Fin S.card → ℕ) : (splitR S rd C).holds m x ↔ C.holds m (merge S x (rd m)) := by
  unfold GCmp.holds
  rw [splitR_form]
  rfl

/-- The least prime factor of `k`, or `N` for `k = 1`. -/
noncomputable def minF (N k : ℕ) : ℕ := if k = 1 then N else Nat.minFac k

/-- For `1 ≤ k` and `p ≤ N`: `k` has no prime factor below `p` iff `p ≤ minF N k`. -/
theorem rough_iff_minF {N k p : ℕ} (hk : 1 ≤ k) (hpN : p ≤ N) : rough p k ↔ p ≤ minF N k := by
  unfold minF
  split_ifs with h
  · subst h
    exact ⟨fun _ => hpN, fun _ q _ hq hd => hq.one_lt.ne' (Nat.dvd_one.1 hd)⟩
  · exact SieveStops2.rough_iff_le_minFac (by omega)

/-- `x_i ≤ minF N (kf m)`. -/
noncomputable def groughK {K : ℕ} (i : Fin K) (kf : ℕ → ℕ) (N : ℕ) : GCmp K where
  c := fun m => Real.log (minF N (kf m))
  e := fun t => -(if t = i then 1 else 0)
  strict := false
  he := fun t => by split_ifs <;> simp

theorem minF_pos {N k : ℕ} (hN : 1 ≤ N) : 0 < minF N k := by
  unfold minF
  split_ifs
  · omega
  · exact Nat.minFac_pos k

theorem groughK_holds {K : ℕ} (i : Fin K) (kf : ℕ → ℕ) {N : ℕ} (hN : 1 ≤ N) (m : ℕ) {x : Fin K → ℕ}
    (hx : ∀ t, 1 ≤ x t) : (groughK i kf N).holds m x ↔ x i ≤ minF N (kf m) := by
  have hpos : (0 : ℝ) < x i := by exact_mod_cast hx i
  have hmf : (0 : ℝ) < minF N (kf m) := by exact_mod_cast minF_pos hN
  unfold GCmp.holds GCmp.form groughK
  simp only [Bool.false_eq_true, ite_false, neg_mul, Finset.sum_neg_distrib, gsum_single, ← sub_eq_add_neg,
    sub_nonneg]
  rw [Real.log_le_log_iff hpos hmf, Nat.cast_le]

/-- The comparisons of a slice `ι`: the region `Ω` and the roughness of `k = m/∏readP`, both on the chain with its part
off `U` read from `m`, and the range `N₁ < m∏x ≤ N₂`. -/
noncomputable def cmpsR {k' : ℕ} (U : Finset (Fin (k' + 1))) (z : ℕ) (ι : Fin Uᶜ.card → ℕ)
    (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℕ) : List (GCmp U.card) :=
  Ω.map (fun C => splitR U (readP z ι) C.const) ++
    [splitR U (readP z ι) (groughK (Fin.last k') (fun m => m / ∏ v, readP z ι m v) N₂),
      grangeLo (N₁ : ℝ), grangeHi (N₂ : ℝ)]

theorem length_cmpsR {k' : ℕ} (U : Finset (Fin (k' + 1))) (z : ℕ) (ι : Fin Uᶜ.card → ℕ)
    (Ω : List (GCmp (k' + 1))) (N₁ N₂ : ℕ) : (cmpsR U z ι Ω N₁ N₂).length = Ω.length + 3 := by
  simp [cmpsR]

/-! ### The bound -/

section TypeII

open Classical

set_option maxHeartbeats 4000000 in
/-- **Chains with part of their product in the reflection of the window.** Assume `RouteOK` and the route's Type II
estimate (`hII`). Fix `e₀ > 0`, `k′`, `J₀` and `Λ₁ ≥ 0`. There are `δ > 0` and `q₀` such that for `q ≥ q₀` and a unit
`a` mod `q`: let `rt` run over the `(k′ + 1)`-tuples of primes up to `N₂ = ⌊2q^L⌋` that satisfy at most `J₀`
comparisons `Ω` (with `m`-parts at most `Λ₁ log q` at `m = 0`), each such tuple strictly decreasing, with entries at
least `q^{e₀}` and `W₀ < ∏_{i∈U} rt_i ≤ W₁`, where `W₁ ≤ N₁ = ⌊q^L⌋`, `q^{w₁L} ≤ ⌊N₁/W₁⌋` and
`⌊N₂/(W₀ + 1)⌋ ≤ q^{w₂L}`. Then the multiples `n ∈ (N₁, N₂]` of `∏rt` with no prime factor below `rt`'s last entry,
summed over `rt`, have `|A − B/φ(q)|` at most `q^{L−δ}/φ(q)`. -/
theorem chainTR_bound [Route] [RouteOK] (hII : TypeIIAt) {e₀ : ℝ} (he₀ : 0 < e₀) (k' J₀ : ℕ) {Λ₁ : ℝ}
    (hΛ₁ : 0 ≤ Λ₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q → ∀ (a : ZMod q), IsUnit a →
      ∀ (U : Finset (Fin (k' + 1))) (Ω : List (GCmp (k' + 1))) (W₀ W₁ : ℕ), Ω.length ≤ J₀ →
      (∀ C ∈ Ω, C.c 0 ≤ Λ₁ * Real.log q) →
      (∀ rt : Fin (k' + 1) → ℕ, (∀ i, (rt i).Prime) → (∀ C ∈ Ω, C.holds 0 rt) →
        StrictAnti rt ∧ (∀ i, (q : ℝ) ^ e₀ ≤ rt i) ∧ W₀ < ∏ i ∈ U, rt i ∧ ∏ i ∈ U, rt i ≤ W₁) →
      W₁ ≤ ⌊(q : ℝ) ^ L⌋₊ →
      (q : ℝ) ^ (w₁ * L) ≤ ((⌊(q : ℝ) ^ L⌋₊ / W₁ : ℕ) : ℝ) →
      ((⌊2 * (q : ℝ) ^ L⌋₊ / (W₀ + 1) : ℕ) : ℝ) ≤ (q : ℝ) ^ (w₂ * L) →
      ‖∑ rt ∈ RTg (k' + 1) ⌊2 * (q : ℝ) ^ L⌋₊ Ω,
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ L⌋₊ ⌊2 * (q : ℝ) ^ L⌋₊,
            dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
  set Kmax : ℕ := ⌈(L + 1) / e₀⌉₊ with hKmax
  set Bs : ℕ := (Kmax + 1) ^ (k' + 1) with hBs
  have hL0 := (L_pos : (0 : ℝ) < L)
  obtain ⟨δ, hδ, q₁, hq₁⟩ := typeII_gcmp' hII (k' + 1) (J₀ + 3) (half_pos he₀)
    (show (0 : ℝ) ≤ Λ₁ + (k' + 2) * (L + 1) by positivity)
  have hev1 := (tendsto_rpow_atTop (half_pos he₀)).eventually_ge_atTop (2 : ℝ)
  have hev2 := (tendsto_rpow_atTop (half_pos hδ)).eventually_ge_atTop (Bs : ℝ)
  have hev3 := (tendsto_rpow_atTop (show (0 : ℝ) < L - w₂ * L by route_num)).eventually_ge_atTop (2 : ℝ)
  have hev4 := (tendsto_rpow_atTop he₀).eventually_ge_atTop (2 : ℝ)
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (hev1.and (hev2.and (hev3.and hev4))))
  refine ⟨δ / 2, half_pos hδ, max (max q₁ q₂) 3, ?_⟩
  intro q _ hq a ha U Ω W₀ W₁ hΩlen hΩc hreg hW₁ hP₁ hP₂
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  obtain ⟨hqe, hqB, hq485, hqe0⟩ := hq₂ q (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq)
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  set N₁ := ⌊(q : ℝ) ^ L⌋₊ with hN₁
  set N₂ := ⌊2 * (q : ℝ) ^ L⌋₊ with hN₂
  have hX1 : (1 : ℝ) ≤ (q : ℝ) ^ L := Real.one_le_rpow (by linarith) (by route_num)
  have hN₁1 : 1 ≤ N₁ := Nat.le_floor (by exact_mod_cast hX1)
  have hN₁N₂ : N₁ ≤ N₂ := Nat.floor_le_floor (by linarith)
  have hN₂1 : 1 ≤ N₂ := le_trans hN₁1 hN₁N₂
  have hN₂le : (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := Nat.floor_le (by positivity)
  have hqe2 : (2 : ℝ) * (q : ℝ) ^ (e₀ / 2) ≤ (q : ℝ) ^ e₀ := by
    have : (q : ℝ) ^ e₀ = (q : ℝ) ^ (e₀ / 2) * (q : ℝ) ^ (e₀ / 2) := by
      rw [← Real.rpow_add hq0]; ring_nf
    rw [this]
    have : (0 : ℝ) ≤ (q : ℝ) ^ (e₀ / 2) := by positivity
    nlinarith
  -- the window's ends
  have hN₂w : (q : ℝ) ^ (w₂ * L) < N₂ := by
    have h1 : (q : ℝ) ^ L = (q : ℝ) ^ (w₂ * L) * (q : ℝ) ^ (L - w₂ * L : ℝ) := by
      rw [← Real.rpow_add hq0]; ring_nf
    have h2 : (1 : ℝ) ≤ (q : ℝ) ^ (w₂ * L) := Real.one_le_rpow (by linarith) (by route_num)
    have h3 : (q : ℝ) ^ L - 1 < N₁ := Nat.sub_one_lt_floor _
    have h4 : (N₁ : ℝ) ≤ N₂ := by exact_mod_cast hN₁N₂
    nlinarith
  have hP₁1 : 1 ≤ N₁ / W₁ := by
    have : (1 : ℝ) ≤ (q : ℝ) ^ (w₁ * L) := Real.one_le_rpow (by linarith) (by route_num)
    exact_mod_cast this.trans hP₁
  have hW₁0 : 0 < W₁ := by
    rcases Nat.eq_zero_or_pos W₁ with h | h
    · rw [h, Nat.div_zero] at hP₁1
      omega
    · exact h
  have hW₀1 : 1 ≤ W₀ := by
    rcases Nat.eq_zero_or_pos W₀ with h | h
    · exfalso
      rw [h, zero_add, Nat.div_one] at hP₂
      linarith
    · exact h
  -- the threshold `z = ⌈q^{e₀}⌉` and the ranks
  set z : ℕ := ⌈(q : ℝ) ^ e₀⌉₊ with hz
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ z := le_trans hqe0 (Nat.le_ceil _)
    exact_mod_cast this
  have hzle : ∀ p : ℕ, (q : ℝ) ^ e₀ ≤ p → z ≤ p := fun p hp => Nat.ceil_le.2 hp
  have hzK : N₂ < z ^ (Kmax + 1) := by
    have hK : (L + 1 : ℝ) ≤ e₀ * (Kmax + 1) := by
      have := Nat.le_ceil ((L + 1) / e₀)
      rw [← hKmax, div_le_iff₀ he₀] at this
      nlinarith
    have hpow : (q : ℝ) ^ (L + 1 : ℝ) ≤ (z : ℝ) ^ (Kmax + 1) := by
      calc (q : ℝ) ^ (L + 1 : ℝ) ≤ (q : ℝ) ^ (e₀ * (Kmax + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) hK
        _ = ((q : ℝ) ^ e₀) ^ (Kmax + 1) := by
            rw [Real.rpow_mul hq0.le, ← Real.rpow_natCast]; push_cast; ring_nf
        _ ≤ (z : ℝ) ^ (Kmax + 1) := pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) _
    have hlt : (N₂ : ℝ) < (q : ℝ) ^ (L + 1 : ℝ) := by
      calc (N₂ : ℝ) ≤ 2 * (q : ℝ) ^ L := hN₂le
        _ < 3 * (q : ℝ) ^ L := by linarith
        _ ≤ (q : ℝ) * (q : ℝ) ^ L := by nlinarith
        _ = (q : ℝ) ^ (L + 1 : ℝ) := by rw [Real.rpow_add hq0, Real.rpow_one]; ring
    exact_mod_cast lt_of_lt_of_le hlt hpow
  -- the chains
  have hRT : ∀ rt ∈ RTg (k' + 1) N₂ Ω, (∀ i, (rt i).Prime) ∧ (∀ C ∈ Ω, C.holds 0 rt) := by
    intro rt hrt
    rw [RTg, Finset.mem_filter, Fintype.mem_piFinset] at hrt
    exact ⟨fun i => (SieveTypeIIU.mem_primesLe.1 (hrt.1 i)).2, hrt.2⟩
  -- `U` is not empty
  by_cases hU0 : U.card = 0
  · rw [Finset.sum_eq_zero, norm_zero]
    · positivity
    intro rt hrt
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    have hUe : U = ∅ := Finset.card_eq_zero.1 hU0
    have := (hreg rt hrtp hrtΩ).2.2.1
    rw [hUe, Finset.prod_empty] at this
    omega
  have hU1 : 1 ≤ U.card := Nat.one_le_iff_ne_zero.2 hU0
  -- each chain: its multiples as cofactors
  have hterm : ∀ rt ∈ RTg (k' + 1) N₂ Ω,
      ∑ n ∈ Finset.Ioc N₁ N₂, dw q a n * (if (∏ i, rt i) ∣ n ∧ rough (rt (Fin.last k')) n then 1 else 0) =
        ∑ k ∈ Finset.Icc 1 N₂, (if rough (rt (Fin.last k')) k ∧ N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
          then dw q a ((∏ i, rt i) * k) else 0) := by
    intro rt hrt
    obtain ⟨hrtp, hrtΩ⟩ := hRT rt hrt
    obtain ⟨hsa, -, -, -⟩ := hreg rt hrtp hrtΩ
    have hW0 : 0 < ∏ i, rt i := Finset.prod_pos fun i _ => (hrtp i).pos
    have hWr : rough (rt (Fin.last k')) (∏ i, rt i) := by
      intro ℓ hℓp hℓ hd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hℓ.prime _).1 hd
      rw [(Nat.prime_dvd_prime_iff_eq hℓ (hrtp i)).1 hi] at hℓp
      have := hsa.antitone (Fin.le_last i)
      omega
    rw [sum_mult_eq (dw q a) hW0 hWr, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hr : rough (rt (Fin.last k')) k
    · have hr' : ∀ p' < rt (Fin.last k'), p'.Prime → ¬ p' ∣ k := hr
      rw [ite_eq_left hr']
      by_cases hc : N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
      · rw [ite_eq_left hc, ite_eq_left ⟨hr, hc⟩]
      · rw [ite_eq_right hc, ite_eq_right fun h => hc h.2]
    · have hr' : ¬ ∀ p' < rt (Fin.last k'), p'.Prime → ¬ p' ∣ k := hr
      rw [ite_eq_right hr', ite_eq_right fun h => hr h.1]
  rw [Finset.sum_congr rfl hterm]
  -- the chains as all tuples, with the region as a condition
  have hall : ∑ rt ∈ RTg (k' + 1) N₂ Ω, ∑ k ∈ Finset.Icc 1 N₂,
      (if rough (rt (Fin.last k')) k ∧ N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
        then dw q a ((∏ i, rt i) * k) else 0) =
      ∑ rt ∈ Fintype.piFinset (fun _ : Fin (k' + 1) => SieveTypeIIU.primesLe N₂), ∑ k ∈ Finset.Icc 1 N₂,
        (if (∀ C ∈ Ω, C.holds 0 rt) ∧ rough (rt (Fin.last k')) k ∧ N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
          then dw q a ((∏ i, rt i) * k) else 0) := by
    rw [RTg, Finset.sum_filter]
    refine Finset.sum_congr rfl fun rt _ => ?_
    by_cases hΩ' : ∀ C ∈ Ω, C.holds 0 rt
    · rw [ite_eq_left hΩ']
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hc : rough (rt (Fin.last k')) k ∧ N₁ < (∏ i, rt i) * k ∧ (∏ i, rt i) * k ≤ N₂
      · rw [ite_eq_left hc, ite_eq_left ⟨hΩ', hc⟩]
      · rw [ite_eq_right hc, ite_eq_right fun h => hc h.2]
    · rw [ite_eq_right hΩ']
      exact (Finset.sum_eq_zero fun k _ => by simp [hΩ']).symm
  rw [hall, sum_pi_merge U]
  -- the part off `U` and `k`, as slices
  have hsl : ∀ x ∈ Fintype.piFinset (fun _ : Fin U.card => SieveTypeIIU.primesLe N₂),
      ∑ b ∈ Fintype.piFinset (fun _ : Fin Uᶜ.card => SieveTypeIIU.primesLe N₂), ∑ k ∈ Finset.Icc 1 N₂,
        (if (∀ C ∈ Ω, C.holds 0 (merge U x b)) ∧ rough (merge U x b (Fin.last k')) k ∧
          N₁ < (∏ i, merge U x b i) * k ∧ (∏ i, merge U x b i) * k ≤ N₂
          then dw q a ((∏ i, merge U x b i) * k) else 0) =
      ∑ ι ∈ slices Uᶜ.card (Kmax + 1), ∑ m ∈ Finset.Icc 1 N₂,
        (if valid z ι m then
          (if (∀ C ∈ Ω, C.holds 0 (merge U x (readP z ι m))) ∧
              rough (merge U x (readP z ι m) (Fin.last k')) (m / ∏ v, readP z ι m v) ∧
              N₁ < (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ∧
              (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ≤ N₂
            then dw q a ((∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v)) else 0) else 0) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    rw [← sum_slices hz2 hzK (fun b k => if (∀ C ∈ Ω, C.holds 0 (merge U x b)) ∧
      rough (merge U x b (Fin.last k')) k ∧ N₁ < (∏ i, merge U x b i) * k ∧ (∏ i, merge U x b i) * k ≤ N₂
      then dw q a ((∏ i, merge U x b i) * k) else 0)]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.mem_piFinset] at hb
    by_cases hc : (∀ C ∈ Ω, C.holds 0 (merge U x b)) ∧ rough (merge U x b (Fin.last k')) k ∧
        N₁ < (∏ i, merge U x b i) * k ∧ (∏ i, merge U x b i) * k ≤ N₂
    · have hrtp : ∀ i, (merge U x b i).Prime := by
        intro i
        obtain ⟨y, rfl⟩ := (eS U).surjective i
        rcases y with u | v
        · rw [merge_inl]; exact (SieveTypeIIU.mem_primesLe.1 (hx u)).2
        · rw [merge_inr]; exact (SieveTypeIIU.mem_primesLe.1 (hb v)).2
      obtain ⟨hsa, hge, -, -⟩ := hreg _ hrtp hc.1
      have hbsa : StrictAnti b := by
        have := hsa.comp_strictMono (eS_inr_strictMono (S := U))
        simpa only [Function.comp_def, merge_inr] using this
      have hbz : ∀ v, z ≤ b v := fun v => by
        have := hge (eS U (Sum.inr v))
        rw [merge_inr] at this
        exact hzle _ this
      have hprod : ∏ i, merge U x b i = (∏ u, x u) * ∏ v, b v := by
        rw [prod_split_nat (S := U)]
        simp only [merge_inl, merge_inr]
      have hx1 : 1 ≤ ∏ u, x u := Finset.one_le_prod fun u _ => (SieveTypeIIU.mem_primesLe.1 (hx u)).2.one_lt.le
      have hbk : (∏ v, b v) * k ≤ N₂ := by
        refine le_trans ?_ hc.2.2.2
        rw [hprod, mul_assoc]
        exact Nat.le_mul_of_pos_left _ hx1
      rw [ite_eq_left (show StrictAnti b ∧ (∀ v, z ≤ b v) ∧ (∏ v, b v) * k ≤ N₂ from ⟨hbsa, hbz, hbk⟩)]
    · rw [ite_eq_right hc]
      split_ifs <;> rfl
  rw [Finset.sum_congr rfl hsl, Finset.sum_comm]
  -- each slice
  have hbound : ∀ ι ∈ slices Uᶜ.card (Kmax + 1),
      ‖∑ x ∈ Fintype.piFinset (fun _ : Fin U.card => SieveTypeIIU.primesLe N₂), ∑ m ∈ Finset.Icc 1 N₂,
        (if valid z ι m then
          (if (∀ C ∈ Ω, C.holds 0 (merge U x (readP z ι m))) ∧
              rough (merge U x (readP z ι m) (Fin.last k')) (m / ∏ v, readP z ι m v) ∧
              N₁ < (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ∧
              (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ≤ N₂
            then dw q a ((∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v)) else 0) else 0)‖ ≤
        (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ) := by
    intro ι hι
    have hιm : StrictMono ι := (Finset.mem_filter.1 hι).2
    rw [Finset.sum_comm]
    set S := (Finset.Ioc (N₁ / W₁) (N₂ / (W₀ + 1))).filter (valid z ι) with hSdef
    -- the facts at a valid `m` and a tuple `x` of primes
    have hfacts : ∀ m, valid z ι m → 1 ≤ m → ∀ x : Fin U.card → ℕ, (∀ u, (x u).Prime) →
        (∀ i, (merge U x (readP z ι m) i).Prime) ∧
        (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) = (∏ u, x u) * m ∧
        1 ≤ m / ∏ v, readP z ι m v ∧ ∏ i ∈ U, merge U x (readP z ι m) i = ∏ u, x u := by
      intro m hv hm1 x hxp
      have hdvd := prod_readP_dvd hιm hv
      have hmem := readP_mem hv
      refine ⟨fun i => ?_, ?_, ?_, ?_⟩
      · obtain ⟨y, rfl⟩ := (eS U).surjective i
        rcases y with u | v
        · rw [merge_inl]; exact hxp u
        · rw [merge_inr]; exact (mem_bigF.1 (hmem v)).1
      · rw [prod_split_nat (S := U)]
        simp only [merge_inl, merge_inr]
        rw [mul_assoc, Nat.mul_div_cancel' hdvd]
      · rcases Nat.eq_zero_or_pos (m / ∏ v, readP z ι m v) with h | h
        · have := Nat.mul_div_cancel' hdvd
          rw [h, mul_zero] at this
          omega
        · exact h
      · rw [prod_S]
        simp only [merge_inl]
    have hsub : S ⊆ Finset.Icc 1 N₂ := by
      intro m hm
      rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hm
      rw [Finset.mem_Icc]
      refine ⟨by omega, le_trans hm.1.2 (Nat.div_le_self _ _)⟩
    rw [← Finset.sum_subset hsub ?_]
    · -- on `S`: the comparisons of the slice
      have hc : ∀ m ∈ S, ∀ x ∈ Fintype.piFinset (fun _ : Fin U.card => SieveTypeIIU.primesLe N₂),
          (if valid z ι m then
            (if (∀ C ∈ Ω, C.holds 0 (merge U x (readP z ι m))) ∧
                rough (merge U x (readP z ι m) (Fin.last k')) (m / ∏ v, readP z ι m v) ∧
                N₁ < (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ∧
                (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ≤ N₂
              then dw q a ((∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v)) else 0) else 0) =
          (if ∀ C ∈ cmpsR U z ι Ω N₁ N₂, C.holds m x then (fun _ => (1 : ℂ)) m * dw q a (m * ∏ u, x u)
            else 0) := by
        intro m hm x hx
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hm
        have hv := hm.2
        have hm1 : 1 ≤ m := by omega
        rw [Fintype.mem_piFinset] at hx
        have hxp : ∀ u, (x u).Prime := fun u => (SieveTypeIIU.mem_primesLe.1 (hx u)).2
        obtain ⟨hrtp, hprod, hk1, -⟩ := hfacts m hv hm1 x hxp
        have hx1 : ∀ u, 1 ≤ x u := fun u => (hxp u).one_lt.le
        have hrt1 : ∀ i, 1 ≤ merge U x (readP z ι m) i := fun i => (hrtp i).one_lt.le
        have hlastN : merge U x (readP z ι m) (Fin.last k') ≤ N₂ := by
          obtain ⟨y, hy⟩ := (eS U).surjective (Fin.last k')
          rw [← hy]
          rcases y with u | v
          · rw [merge_inl]; exact (SieveTypeIIU.mem_primesLe.1 (hx u)).1
          · rw [merge_inr]
            obtain ⟨-, hpm, -, -⟩ := mem_bigF.1 (readP_mem hv v)
            exact le_trans (Nat.le_of_dvd (by omega) hpm) (le_trans hm.1.2 (Nat.div_le_self _ _))
        have hN₁0 : (0 : ℝ) < N₁ := by exact_mod_cast hN₁1
        have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast hN₂1
        have hcast : (((∏ u, x u) * m : ℕ) : ℝ) = (m : ℝ) * ∏ u, (x u : ℝ) := by push_cast; ring
        have hiff : (∀ C ∈ cmpsR U z ι Ω N₁ N₂, C.holds m x) ↔
            (∀ C ∈ Ω, C.holds 0 (merge U x (readP z ι m))) ∧
              rough (merge U x (readP z ι m) (Fin.last k')) (m / ∏ v, readP z ι m v) ∧
              N₁ < (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ∧
              (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ≤ N₂ := by
          unfold cmpsR
          simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
            false_implies, implies_true, and_true, splitR_holds, GCmp.const_holds,
            groughK_holds _ _ hN₂1 m hrt1, grangeLo_holds hN₁0 hm1 hx1, grangeHi_holds hN₂0 hm1 hx1]
          rw [hprod, ← rough_iff_minF hk1 hlastN]
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨h1, h2, ?_, ?_⟩
            · have : (N₁ : ℝ) < (((∏ u, x u) * m : ℕ) : ℝ) := by rw [hcast]; exact h3
              exact_mod_cast this
            · have : (((∏ u, x u) * m : ℕ) : ℝ) ≤ N₂ := by rw [hcast]; exact h4
              exact_mod_cast this
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨h1, h2, ?_, ?_⟩
            · rw [← hcast]; exact_mod_cast h3
            · rw [← hcast]; exact_mod_cast h4
        rw [ite_eq_left hv]
        by_cases hcond : (∀ C ∈ Ω, C.holds 0 (merge U x (readP z ι m))) ∧
            rough (merge U x (readP z ι m) (Fin.last k')) (m / ∏ v, readP z ι m v) ∧
            N₁ < (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ∧
            (∏ i, merge U x (readP z ι m) i) * (m / ∏ v, readP z ι m v) ≤ N₂
        · rw [ite_eq_left hcond, ite_eq_left (hiff.2 hcond), hprod, one_mul, mul_comm]
        · rw [ite_eq_right hcond, ite_eq_right fun h => hcond (hiff.1 h)]
      rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl (hc m hm)]
      have hlog : ∀ (t c : ℝ), 0 < t → t ≤ (q : ℝ) ^ c → Real.log t ≤ c * Real.log q := fun t c ht h => by
        rw [← Real.log_rpow hq0]
        exact Real.log_le_log ht h
      have hN₂q : (N₂ : ℝ) ≤ (q : ℝ) ^ (L + 1 : ℝ) := by
        rw [Real.rpow_add hq0, Real.rpow_one]
        have h0 : (0 : ℝ) ≤ (q : ℝ) ^ L := by positivity
        have h1 : 2 * (q : ℝ) ^ L ≤ (q : ℝ) ^ L * q := by
          have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ q by linarith) h0
          linarith
        linarith
      have hlN₂ := hlog N₂ (L + 1) (by exact_mod_cast hN₂1) hN₂q
      have hlN₂0 : 0 ≤ Real.log N₂ := Real.log_nonneg (by exact_mod_cast hN₂1)
      have hΛl : 0 ≤ Λ₁ * Real.log q := mul_nonneg hΛ₁ hlogq.le
      -- the reading's logs
      have hrdlog : ∀ m ∈ S, ∀ (e : Fin Uᶜ.card → ℝ), (∀ v, e v = -1 ∨ e v = 0 ∨ e v = 1) →
          ∑ v, e v * Real.log (readP z ι m v) ≤ (k' + 1) * Real.log N₂ := by
        intro m hm e he
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hm
        have hv := hm.2
        have hmN : m ≤ N₂ := le_trans hm.1.2 (Nat.div_le_self _ _)
        have hterm' : ∀ v, e v * Real.log (readP z ι m v) ≤ Real.log N₂ := by
          intro v
          obtain ⟨hp, hpm, -, -⟩ := mem_bigF.1 (readP_mem hv v)
          have h1 : (1 : ℝ) ≤ readP z ι m v := by exact_mod_cast hp.one_lt.le
          have h2 : (readP z ι m v : ℝ) ≤ N₂ := by
            exact_mod_cast le_trans (Nat.le_of_dvd (by omega) hpm) hmN
          have hl0 : 0 ≤ Real.log (readP z ι m v) := Real.log_nonneg h1
          have hl1 : Real.log (readP z ι m v) ≤ Real.log N₂ := Real.log_le_log (by linarith) h2
          rcases he v with h | h | h <;> rw [h] <;> linarith
        calc ∑ v, e v * Real.log (readP z ι m v) ≤ ∑ _v : Fin Uᶜ.card, Real.log N₂ :=
              Finset.sum_le_sum fun v _ => hterm' v
          _ = Uᶜ.card * Real.log N₂ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ (k' + 1) * Real.log N₂ := by
              have : (Uᶜ.card : ℝ) ≤ k' + 1 := by
                have := Finset.card_le_univ Uᶜ
                rw [Fintype.card_fin] at this
                exact_mod_cast this
              exact mul_le_mul_of_nonneg_right this hlN₂0
      have hB : (Λ₁ + (k' + 2) * (L + 1)) * Real.log q =
          Λ₁ * Real.log q + (k' + 1) * ((L + 1) * Real.log q) + (L + 1) * Real.log q := by ring
      have hkL : (k' + 1 : ℝ) * Real.log N₂ ≤ (k' + 1) * ((L + 1) * Real.log q) :=
        mul_le_mul_of_nonneg_left hlN₂ (by positivity)
      have hL1 : 0 ≤ (L + 1) * Real.log q := by positivity
      have hkL0 : 0 ≤ (k' + 1 : ℝ) * ((L + 1) * Real.log q) := by positivity
      refine hq₁ q hq1 a ha (N₁ / W₁) (N₂ / (W₀ + 1)) S (Finset.filter_subset _ _) hP₁ hP₂ (fun _ => 1)
        (fun _ => by simp) U.card hU1 (by have := Finset.card_le_univ U; simp at this; omega)
        (cmpsR U z ι Ω N₁ N₂) (by rw [length_cmpsR]; omega) ?_ ?_
      · -- the `m`-parts
        intro C hC m hm
        have hm' := hm
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hm'
        have hm1 : 1 ≤ m := by omega
        have hmN : m ≤ N₂ := le_trans hm'.1.2 (Nat.div_le_self _ _)
        have hlm : Real.log m ≤ Real.log N₂ := Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmN)
        have hlm0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
        unfold cmpsR at hC
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at hC
        rcases hC with ⟨C₀, hC₀, rfl⟩ | rfl | rfl | rfl
        · show C₀.c 0 + ∑ v, C₀.e (eS U (Sum.inr v)) * Real.log (readP z ι m v) ≤ _
          have := hrdlog m hm (fun v => C₀.e (eS U (Sum.inr v))) fun v => C₀.he _
          have := hΩc C₀ hC₀
          rw [hB]
          linarith
        · show Real.log (minF N₂ (m / ∏ v, readP z ι m v)) + ∑ v, (groughK (Fin.last k')
            (fun m => m / ∏ v, readP z ι m v) N₂).e (eS U (Sum.inr v)) * Real.log (readP z ι m v) ≤ _
          have h1 := hrdlog m hm (fun v => (groughK (Fin.last k') (fun m => m / ∏ v, readP z ι m v) N₂).e
            (eS U (Sum.inr v))) fun v => (groughK (Fin.last k') (fun m => m / ∏ v, readP z ι m v) N₂).he _
          have h2 : Real.log (minF N₂ (m / ∏ v, readP z ι m v)) ≤ Real.log N₂ := by
            have hpos := minF_pos (k := m / ∏ v, readP z ι m v) hN₂1
            refine Real.log_le_log (by exact_mod_cast hpos) ?_
            have : minF N₂ (m / ∏ v, readP z ι m v) ≤ N₂ := by
              unfold minF
              split_ifs with h
              · exact le_rfl
              · exact le_trans (Nat.minFac_le (by
                  have := (hfacts m hm'.2 hm1 (fun _ => 2) (fun _ => Nat.prime_two)).2.2.1
                  omega)) (le_trans (Nat.div_le_self _ _) hmN)
            exact_mod_cast this
          rw [hB]
          linarith
        · show Real.log m - Real.log N₁ ≤ _
          have := Real.log_nonneg (show (1 : ℝ) ≤ N₁ by exact_mod_cast hN₁1)
          rw [hB]
          linarith
        · show Real.log N₂ - Real.log m ≤ _
          rw [hB]
          linarith
      · -- the support
        intro m hm x hx hcm
        have hm' := hm
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc] at hm'
        have hm1 : 1 ≤ m := by omega
        obtain ⟨hrtp, -, -, -⟩ := hfacts m hm'.2 hm1 x hx
        have hx1 : ∀ u, 1 ≤ x u := fun u => (hx u).one_lt.le
        have hN₂0 : (0 : ℝ) < N₂ := by exact_mod_cast hN₂1
        unfold cmpsR at hcm
        simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons, List.mem_nil_iff,
          false_implies, implies_true, and_true, splitR_holds, GCmp.const_holds] at hcm
        obtain ⟨hΩ', -, -, hhi⟩ := hcm
        obtain ⟨-, hge, -, -⟩ := hreg _ hrtp hΩ'
        refine ⟨fun u => ?_, ?_⟩
        · have := hge (eS U (Sum.inl u))
          rw [merge_inl] at this
          linarith
        · exact ((grangeHi_holds hN₂0 hm1 hx1).1 hhi).trans hN₂le
    · -- off `S` the terms vanish
      intro m hm hmS
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Fintype.mem_piFinset] at hx
      by_cases hv : valid z ι m
      · rw [ite_eq_left hv, ite_eq_right]
        rintro ⟨hΩ', -, hlo, hhi⟩
        apply hmS
        have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
        have hxp : ∀ u, (x u).Prime := fun u => (SieveTypeIIU.mem_primesLe.1 (hx u)).2
        obtain ⟨hrtp, hprod, -, hU⟩ := hfacts m hv hm1 x hxp
        obtain ⟨-, -, hW₀', hW₁'⟩ := hreg _ hrtp hΩ'
        rw [hU] at hW₀' hW₁'
        rw [hprod] at hlo hhi
        rw [hSdef, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨?_, ?_⟩, hv⟩
        · rw [Nat.div_lt_iff_lt_mul hW₁0]
          calc N₁ < (∏ u, x u) * m := hlo
            _ ≤ W₁ * m := Nat.mul_le_mul_right m hW₁'
            _ = m * W₁ := Nat.mul_comm _ _
        · rw [Nat.le_div_iff_mul_le (by omega)]
          calc m * (W₀ + 1) ≤ m * ∏ u, x u := Nat.mul_le_mul_left m hW₀'
            _ = (∏ u, x u) * m := Nat.mul_comm _ _
            _ ≤ N₂ := hhi
      · rw [ite_eq_right hv]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hbound).trans ?_
  rw [nsmul_eq_mul]
  have hcard : ((slices Uᶜ.card (Kmax + 1)).card : ℝ) ≤ Bs := by
    have h1 := card_slices_le Uᶜ.card (Kmax + 1)
    have h2 : (Kmax + 1) ^ Uᶜ.card ≤ Bs := by
      rw [hBs]
      refine Nat.pow_le_pow_right (by omega) ?_
      have := Finset.card_le_univ Uᶜ
      rw [Fintype.card_fin] at this
      exact this
    exact_mod_cast h1.trans h2
  calc ((slices Uᶜ.card (Kmax + 1)).card : ℝ) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ))
      ≤ (q : ℝ) ^ (δ / 2) * ((q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ)) :=
        mul_le_mul_of_nonneg_right (hcard.trans hqB) (by positivity)
    _ = (q.totient : ℝ)⁻¹ * (q : ℝ) ^ (L - δ / 2) := by
        rw [mul_left_comm, ← Real.rpow_add hq0]
        congr 2
        ring

end TypeII

end SieveChainR
