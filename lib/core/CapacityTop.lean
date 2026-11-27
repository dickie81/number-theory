import CapacityWeights

/-!
# The top components of the translated path polynomials (E2, E3 of T3)

The weight-`μ_i` component of the generic translate (through the first `i` letters) of a path polynomial `Ψ(P, I)`
factors as `±det(g)^e·Ψ(P|_{≤i}, canonical)·Φ(P, I)` up to a power of a fixed non-zero constant, with `Φ(P, I)` the
image of a path polynomial of an *extended word* under an injective substitution; hence these top components are
linearly independent over a domain (E3, `top_linearIndependent`).

**Conventions** (those of `CapacityWeights`). The *dual form* of the column `c` (`dstep`, `dinit`): the state starts at
`[univ]` (`c ≥ 1`) or `[∅]` (`c ≤ 0`), is wedged with the letter vector when the height drops and contracted when it
grows; it is the Hodge dual of the column state for `c ≥ 1` and the column state itself for `c ≤ 0`
(`colK_eq_dual`). Its wedge steps sit at covector letters, so through the prefix it transforms by `Aw false = gᵀ`.

**Main results.**
* *Top components multiply* (`top_comp_prod`): if the weights of each factor are dominated by `τ_c`, the weight-`Στ_c`
  component of the product is the product of the weight-`τ_c` components, through the height `hgt` (strictly monotone
  for dominance, `comp_eq_hcomp`, `hcomp_prod`).
* *(E2) The top component of a column* (`col_top`): `κ_c·[gtr D_c(N)]_{τ_c} = det(g)^{#con}·D_c(i)(T_c)·Φ_c`, with
  `T_c = [colH μ_i c, n)` the coordinate of top weight, `κ_c = W_{gᵀ}(univ)(univ)` (`c ≥ 1`) or `1`, and
  `Φ_c = runFrom (W_{gᵀ} T_c)` the later letters applied to the wedge of the rows `T_c` of `gᵀ`.
* *The extended word* (`xvec`, `xB`, `xmu`, `xpath`, `xfill`): `n` covector letters removing the rows of `μ₀ − L` from
  the bottom (`L ≥ μ₀`), then the letters `i, i + 1, …` with the path `μ_{i + u} − L` and the filling shifted by `L`.
  Its column states after the `n` letters are `[univ]` (`c' ≥ 1`, `xprefix_pos`) or `±` the wedge of rows `T` of the
  letter matrix `Zx` (`xprefix_neg`), and the substitution `xsub` (letter `j < n` ↦ column `n − 1 − j` of `g`, letter
  `n + u` ↦ letter `i + u`) is injective (`xsub_injective`: a renaming, then `R[x ⊕ g] ≅ R[g][x]`) and carries `Zx`
  to `gᵀ` (`xsub_W`). Hence `Φ_c = η_c·xsub(D'_{c − L})` (`xcol_phi`) and, column by column and then over a common
  window, `(Π κ_c)·[gtr Ψ(P, I)]_{μ₀} = ±det(g)^e·Ψ(P|_{≤i}, can)·(Π_{c > L} κ')·xsub(Ψ'(P', I'))`
  (`col_identity`, `top_identity`).
* *(E3)* `top_linearIndependent`: with `tensor_indep` (independent families in disjoint variables over any ring) the
  prefix fibres separate, and inside a fibre the extended indices are distinct (`ext_injective`), so the extended path
  basis and the injectivity of `xsub` conclude. Generic `g` is essential.
-/

namespace CapacitySpan

open MvPolynomial Finset TwistedDegree PathBasis TwistWeights CapStates

noncomputable section

/-! ## Top components multiply -/

section Top

variable {σ B : Type*} [CommRing B] {n : ℕ}

/-- **The height as an additive map.** -/
def hgtHom : (Fin n → ℤ) →+ ℤ where
  toFun := hgt
  map_zero' := by simp [hgt]
  map_add' := hgt_add

/-- **The height of a weight** is the scalar weight for the heights of the variables. -/
theorem weight_hgt (w : σ → Fin n → ℤ) (u : σ →₀ ℕ) :
    Finsupp.weight (fun v => hgt (w v)) u = hgt (Finsupp.weight w u) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  change _ = hgtHom _
  rw [map_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [map_nsmul]; rfl

/-- **A component at a dominating weight is a height component.** -/
theorem comp_eq_hcomp (w : σ → Fin n → ℤ) {f : MvPolynomial σ B} {τ : Fin n → ℤ}
    (hf : WtIn w f {ν | DomLe ν τ}) :
    weightedHomogeneousComponent w τ f = weightedHomogeneousComponent (fun v => hgt (w v)) (hgt τ) f := by
  classical
  ext u
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_hgt]
  by_cases hu : f.coeff u = 0
  · simp [hu]
  · have hd : DomLe (Finsupp.weight w u) τ := hf u (mem_support_iff.2 hu)
    have e : Finsupp.weight w u = τ ↔ hgt (Finsupp.weight w u) = hgt τ :=
      ⟨fun h => by rw [h], fun h => hd.eq_of_hgt_le h.ge⟩
    simp only [e]

/-- **The top height components multiply.** -/
theorem hcomp_mul (h : σ → ℤ) {p q : MvPolynomial σ B} {dp dq : ℤ} (hp : ∀ u ∈ p.support, Finsupp.weight h u ≤ dp)
    (hq : ∀ u ∈ q.support, Finsupp.weight h u ≤ dq) :
    weightedHomogeneousComponent h (dp + dq) (p * q) =
      weightedHomogeneousComponent h dp p * weightedHomogeneousComponent h dq q := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  simp only [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    by_cases hp0 : p.coeff x.1 = 0
    · simp [hp0]
    by_cases hq0 : q.coeff x.2 = 0
    · simp [hq0]
    have h1 := hp x.1 (mem_support_iff.2 hp0)
    have h2 := hq x.2 (mem_support_iff.2 hq0)
    have h3 : Finsupp.weight h x.1 + Finsupp.weight h x.2 = dp + dq := by
      rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hx, hd]
    rw [ite_eq_left_iff.2 fun h => absurd (by omega) h, ite_eq_left_iff.2 fun h => absurd (by omega) h]
  · refine (Finset.sum_eq_zero fun x hx => ?_).symm
    by_cases h1 : Finsupp.weight h x.1 = dp
    · by_cases h2 : Finsupp.weight h x.2 = dq
      · exact absurd (by rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, map_add, h1, h2]) hd
      · rw [ite_eq_right_iff.2 fun h => absurd h h2, mul_zero]
    · rw [ite_eq_right_iff.2 fun h => absurd h h1, zero_mul]

/-- **The heights of a product** are bounded by the sum of the bounds. -/
theorem prod_weight_le (h : σ → ℤ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ B) (d : ι → ℤ)
    (hf : ∀ c ∈ s, ∀ u ∈ (f c).support, Finsupp.weight h u ≤ d c) :
    ∀ u ∈ (∏ c ∈ s, f c).support, Finsupp.weight h u ≤ ∑ c ∈ s, d c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro u hu
    rw [prod_empty] at hu
    have hu0 : u = 0 := by
      by_contra hne
      exact mem_support_iff.1 hu (by simp [coeff_one, Ne.symm hne])
    simp [hu0]
  | insert a s ha ih =>
    intro u hu
    rw [prod_insert ha] at hu
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hu)
    rw [map_add, sum_insert ha]
    exact add_le_add (hf a (mem_insert_self a s) u1 hu1)
      (ih (fun c hc => hf c (mem_insert_of_mem hc)) u2 hu2)

/-- **The top height components of a product multiply.** -/
theorem hcomp_prod (h : σ → ℤ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ B) (d : ι → ℤ)
    (hf : ∀ c ∈ s, ∀ u ∈ (f c).support, Finsupp.weight h u ≤ d c) :
    weightedHomogeneousComponent h (∑ c ∈ s, d c) (∏ c ∈ s, f c) =
      ∏ c ∈ s, weightedHomogeneousComponent h (d c) (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, prod_empty, prod_empty]
    exact weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_one B h) |>.trans (by simp)
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha, prod_insert ha,
      hcomp_mul h (hf a (mem_insert_self a s)) (prod_weight_le h s f d fun c hc => hf c (mem_insert_of_mem hc)),
      ih fun c hc => hf c (mem_insert_of_mem hc)]

/-- **(Top multiplicativity)** if the weights of each factor are dominated by `τ_c`, the weight-`Σ τ_c` component of
the product is the product of the weight-`τ_c` components. -/
theorem top_comp_prod (w : σ → Fin n → ℤ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ B)
    (τ : ι → Fin n → ℤ) (hf : ∀ c ∈ s, WtIn w (f c) {ν | DomLe ν (τ c)}) :
    weightedHomogeneousComponent w (∑ c ∈ s, τ c) (∏ c ∈ s, f c) =
      ∏ c ∈ s, weightedHomogeneousComponent w (τ c) (f c) := by
  rw [comp_eq_hcomp w (wtIn_prod w s f τ hf)]
  have e : hgt (∑ c ∈ s, τ c) = ∑ c ∈ s, hgt (τ c) := by
    change hgtHom _ = _
    rw [map_sum]; rfl
  rw [e, hcomp_prod _ s f _ fun c hc u hu => ?_]
  · exact Finset.prod_congr rfl fun c hc => (comp_eq_hcomp w (hf c hc)).symm
  · rw [weight_hgt]
    exact (hf c hc u hu).hgt_le

end Top

/-! ## The dual form of a column -/

section Dual

variable {Λ : Type*} [CommRing Λ] {n : ℕ}

/-- **The dual step of the column `c`**: wedge if the height drops, contract if it grows. -/
def dstep (μ : ℕ → Fin n → ℤ) (c : ℤ) (u : ℕ) : Step :=
  if colH (μ (u + 1)) c < colH (μ u) c then .wed else if colH (μ u) c < colH (μ (u + 1)) c then .con else .keep

/-- **The dual initial state**: `[univ]` for `c ≥ 1`, `[∅]` for `c ≤ 0`. -/
def dinit (c : ℤ) : Finset (Fin n) → Λ := if 1 ≤ c then fun J => if J = univ then 1 else 0 else st0

/-- **Scaling the initial state scales the run.** -/
theorem run_init_smul (y : ℕ → Fin n → Λ) (st : ℕ → Step) (S0 : Finset (Fin n) → Λ) (p : Λ) :
    ∀ t J, run y st (fun J => p * S0 J) t J = p * run y st S0 t J := by
  intro t
  induction t with
  | zero => intro J; rfl
  | succ t ih =>
    intro J
    rw [run_succ, run_succ, show run y st (fun J => p * S0 J) t = fun J => p * run y st S0 t J from funext ih,
      app_smul]

/-- **The column state is the dual form** (`c ≤ 0`) or its Hodge dual (`c ≥ 1`). -/
theorem colK_eq_dual (y : ℕ → Fin n → Λ) (μ : ℕ → Fin n → ℤ) (c : ℤ) (t : ℕ) (K : Finset (Fin n)) :
    run y (colStep μ c) st0 t K = (if 1 ≤ c then hsg Kᶜ * hsg (univ : Finset (Fin n)) else 1) *
      run y (dstep μ c) (dinit c) t (if 1 ≤ c then Kᶜ else K) := by
  by_cases hc : 1 ≤ c
  · simp only [hc, ite_true]
    have hst : dstep μ c = fun u => stepSwap (colStep μ c u) := by
      funext u
      unfold dstep colStep stepSwap
      simp only [hc, ite_true]
      split_ifs <;> first | rfl | omega
    have h0 : (fun J : Finset (Fin n) => (hsg J : Λ) * st0 Jᶜ) =
        fun J => hsg (univ : Finset (Fin n)) * dinit c J := by
      funext J
      simp only [st0, dinit, hc, ite_true, compl_eq_empty_iff]
      split_ifs with h <;> simp [h]
    have h := run_hodge y (colStep μ c) st0 t Kᶜ
    rw [← hst, h0, run_init_smul, compl_compl] at h
    have h2 := hsg_mul_self (Λ := Λ) Kᶜ
    linear_combination (-(hsg Kᶜ : Λ)) * h - run y (colStep μ c) st0 t K * h2
  · simp only [hc, ite_false, one_mul]
    have hst : dstep μ c = colStep μ c := by
      funext u
      unfold dstep colStep
      simp only [hc, ite_false]
      split_ifs <;> first | rfl | omega
    rw [hst]
    simp only [dinit, hc, ite_false]

variable {N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The dual steps of a Pieri path**: wedges at covector letters, contractions at vector letters. -/
theorem dstep_vec (P : PieriPath n N vec B) (c : ℤ) {u : ℕ} (hu : u < N) :
    (dstep P.mu c u = .wed → vec u = false) ∧ (dstep P.mu c u = .con → vec u = !false) := by
  have hs := P.colH_step hu c
  have hg : colH (P.mu u) c < colH (P.mu (u + 1)) c → vec u = true := fun h => by
    cases hv : vec u
    · have := (hs.2 hv).1; omega
    · rfl
  have hd : colH (P.mu (u + 1)) c < colH (P.mu u) c → vec u = false := fun h => by
    cases hv : vec u
    · rfl
    · have := (hs.1 hv).1; omega
  unfold dstep
  by_cases h1 : colH (P.mu (u + 1)) c < colH (P.mu u) c
  · simp [h1, hd h1]
  · by_cases h2 : colH (P.mu u) c < colH (P.mu (u + 1)) c
    · simp [h1, h2, hg h2]
    · simp [h1, h2]

end Dual

/-! ## (E2) The top component of a column -/

section ColTop

variable {R : Type*} [CommRing R] {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The coordinate of top weight** of the column `c` in the dual form: `[colH λ c, n)`. -/
def Tset (lam : Fin n → ℤ) (c : ℤ) : Finset (Fin n) := (univ.filter fun a : Fin n => a.val < colH lam c)ᶜ

/-- **The dual shift**: `𝟙` for `c ≥ 1`, `0` for `c ≤ 0`. -/
def dshift (c : ℤ) : Fin n → ℤ := if 1 ≤ c then fun _ => 1 else 0

/-- **The constant of the dual initial state**: `Λ_{gᵀ} D_c(0) = κ_c·D_c(0)`. -/
def kap (c : ℤ) : SymbolData.GenCoeff ℕ R n := if 1 ≤ c then W (Aw (R := R) false) univ univ else 1

/-- **The top weight in dual form**: `τ_c = −[T_c] + dshift c`. -/
theorem tau_eq_dual (lam : Fin n → ℤ) (c : ℤ) : tau lam c = (-1 : ℤ) • ind (Tset lam c) + dshift c := by
  funext a
  simp only [tau, ind, Tset, dshift, mem_compl, mem_filter, mem_univ, true_and, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  by_cases hc : 1 ≤ c
  · simp only [hc, ite_true, show ¬ c ≤ 0 by omega, ite_false]
    split_ifs <;> simp
  · simp only [hc, ite_false, show c ≤ 0 by omega, ite_true, Pi.zero_apply]
    split_ifs <;> simp

/-- **The dual initial state is an eigenstate**: `Λ_{gᵀ} D_c(0) = κ_c·D_c(0)`. -/
theorem Lam_dinit (c : ℤ) (K : Finset (Fin n)) :
    Lam (Aw (R := R) false) (dinit c) K = kap c * dinit c K := by
  by_cases hc : 1 ≤ c
  · simp only [kap, dinit, hc, ite_true, Lam_def]
    rw [Finset.sum_eq_single univ (fun J _ hJ => by simp [hJ]) (by simp), ite_eq_left_iff.2 fun h => absurd rfl h,
      one_mul]
    by_cases hK : K = univ
    · rw [hK]; simp
    · rw [W_isDeg _ univ K fun h => hK (Finset.eq_univ_of_card K (by rw [h]; simp))]
      simp [hK]
  · simp only [kap, dinit, hc, ite_false]
    exact Lam_st0 _ K

/-- **The constant `κ_c` has weight `0`.** -/
theorem kap_isWH (vec : ℕ → Bool) (S : Set ℕ) (c : ℤ) :
    IsWeightedHomogeneous (twWt vec S) (kap (R := R) (n := n) c) 0 := by
  unfold kap
  split_ifs
  · exact W_Aw_isWH vec S false univ univ
  · exact isWeightedHomogeneous_one _ _

/-- **The dual initial state has the weights `−[J] + dshift c`.** -/
theorem dinit_isWH (w : ℕ × Fin n → Fin n → ℤ) (c : ℤ) (J : Finset (Fin n)) :
    IsWeightedHomogeneous w (dinit c J : SymbolData.GenCoeff ℕ R n)
      ((if false then 1 else -1 : ℤ) • ind J + dshift c) := by
  by_cases hc : 1 ≤ c
  · simp only [dinit, dshift, hc, ite_true, Bool.false_eq_true, ite_false]
    by_cases hJ : J = univ
    · subst hJ
      have : (-1 : ℤ) • ind (univ : Finset (Fin n)) + (fun _ => 1) = 0 := by funext a; simp [ind]
      rw [this]; simpa using isWeightedHomogeneous_one (MvPolynomial (Fin n × Fin n) R) w
    · simpa [hJ] using isWeightedHomogeneous_zero (MvPolynomial (Fin n × Fin n) R) w _
  · simp only [dinit, dshift, hc, ite_false]
    exact isWH_st0 w _ J

/-- **(E2) The top component of a column in dual form**:
`κ_c·[gtr D_c(N)(K)]_{τ_c} = det(g)^{#con}·D_c(i)(T_c)·Φ_c(K)`, `Φ_c = runFrom (W_{gᵀ} T_c)`. -/
theorem col_top (P : PieriPath n N vec B) {i : ℕ} (hi : i ≤ N) (c : ℤ) (K : Finset (Fin n)) :
    kap c * weightedHomogeneousComponent (twWt vec (Set.Iio i)) (tau (P.mu i) c)
      (gtr (R := R) vec (Set.Iio i) (run (fun t a => X (t, a)) (dstep P.mu c) (dinit c) N K)) =
    MvPolynomial.C (genMat R n).det ^ ncon (dstep P.mu c) i *
      run (Yv (R := R)) (dstep P.mu c) (dinit c) i (Tset (P.mu i) c) *
      runFrom (Yv (R := R)) (dstep P.mu c) i (W (Aw false) (Tset (P.mu i) c)) (N - i) K := by
  set w := twWt (n := n) vec (Set.Iio i)
  set st := dstep P.mu c
  have hst : ∀ u < i, (st u = .wed → vec u = false) ∧ (st u = .con → vec u = !false) :=
    fun u hu => dstep_vec P c (by omega)
  have hy0 : ∀ u, i ≤ u → ∀ a, IsWeightedHomogeneous w (Yv (R := R) u a) 0 := fun u hu a => isWH_X_ge vec hu a
  -- the translate of the run, split at `i`
  have hgd : (fun J => gtr (R := R) vec (Set.Iio i) (dinit c J : MvPolynomial (ℕ × Fin n) R)) =
      (dinit c : Finset (Fin n) → SymbolData.GenCoeff ℕ R n) := by
    funext J
    unfold dinit
    split_ifs <;> simp [st0]
  have hsplit : gtr (R := R) vec (Set.Iio i) (run (fun t a => X (t, a)) st (dinit c) N K) =
      runFrom (Yv (R := R)) st i (run (fun t a => gtr (R := R) (n := n) vec (Set.Iio i) (X (t, a))) st
        (dinit c) i) (N - i) K := by
    rw [map_run, hgd]
    have h := run_add (fun t a => gtr (R := R) (n := n) vec (Set.Iio i) (X (t, a))) st (dinit c) i (N - i)
    rw [Nat.add_sub_cancel' hi] at h
    rw [h]
    exact congrFun (runFrom_congr _ _ _ _ fun u hu => gtr_ge_eq vec hu) K
  have hCE : (fun K => kap c * run (fun t a => gtr (R := R) (n := n) vec (Set.Iio i) (X (t, a))) st (dinit c) i K) =
      fun K => MvPolynomial.C (genMat R n).det ^ ncon st i * Lam (Aw false) (run (Yv (R := R)) st (dinit c) i) K :=
    funext fun K => gtr_run vec false hst (Lam_dinit c) K
  have hdet : IsWeightedHomogeneous w (MvPolynomial.C (genMat R n).det ^ ncon st i : SymbolData.GenCoeff ℕ R n) 0 := by
    simpa using (isWeightedHomogeneous_C w (genMat R n).det).pow (ncon st i)
  -- the component of the stage-`i` state
  have hS : ∀ J, IsWeightedHomogeneous w (run (Yv (R := R)) st (dinit c) i J)
      ((if false then 1 else -1 : ℤ) • ind J + dshift c) :=
    fun J => run_isWH_prefix vec false hst (dshift c) (fun J => dinit_isWH w c J) J
  have hS' : ∀ J, IsWeightedHomogeneous w (run (Yv (R := R)) st (dinit c) i J) (-ind J + dshift c) := fun J => by
    have := hS J
    simp only [Bool.false_eq_true, ite_false, neg_smul, one_smul] at this
    exact this
  have htau : tau (P.mu i) c = -ind (Tset (P.mu i) c) + dshift c := by
    rw [tau_eq_dual, neg_smul, one_smul]
  have hcompS : (fun K => weightedHomogeneousComponent w (tau (P.mu i) c)
      (Lam (Aw false) (run (Yv (R := R)) st (dinit c) i) K)) =
      fun K => run (Yv (R := R)) st (dinit c) i (Tset (P.mu i) c) * W (Aw false) (Tset (P.mu i) c) K := by
    funext K
    rw [Lam_def]
    simp only [map_sum]
    rw [Finset.sum_eq_single (Tset (P.mu i) c)]
    · rw [mul_comm, comp_mul_of_isWH0 w (W_Aw_isWH vec _ false _ _), htau,
        (hS' _).weightedHomogeneousComponent_same, mul_comm]
    · intro J _ hJ
      rw [mul_comm, comp_mul_of_isWH0 w (W_Aw_isWH vec _ false _ _), htau,
        (hS' J).weightedHomogeneousComponent_ne _ fun h => hJ (ind_injective ?_), mul_zero]
      have h' := congrArg (fun f => -(f - dshift (n := n) c)) h
      simpa using h'.symm
    · simp
  rw [hsplit, ← comp_mul_of_isWH0 w (kap_isWH vec _ c), ← runFrom_smul, hCE, runFrom_smul,
    comp_mul_of_isWH0 w hdet, comp_runFrom w st hy0, hcompS, runFrom_smul, mul_assoc]

end ColTop

/-! ## The extended word -/

section Ext

variable {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The flags of the extended word**: `n` covector letters, then the letters `i, i + 1, …`. -/
def xvec (i n : ℕ) (vec : ℕ → Bool) : ℕ → Bool := fun j => if j < n then false else vec (i + (j - n))

/-- **The degrees of the extended word**: the letter `j < n` removes the row `n − 1 − j` of `μ₀ − L`. -/
def xB (i : ℕ) (B : ℕ → ℕ) (μ₀ : Fin n → ℤ) (L : ℤ) : ℕ → ℕ :=
  fun j => if h : j < n then (L - μ₀ ⟨n - 1 - j, by omega⟩).toNat else B (i + (j - n))

/-- **The weights of the extended path**: the rows `≥ n − j` of `μ₀ − L` after `j < n` letters, then
`μ_{i + (j − n)} − L`. -/
def xmu (i : ℕ) (μ : ℕ → Fin n → ℤ) (μ₀ : Fin n → ℤ) (L : ℤ) : ℕ → Fin n → ℤ := fun j a =>
  if j < n then (if n - j ≤ a.val then μ₀ a - L else 0) else μ (i + (j - n)) a - L

/-- **A shift preserves strips.** -/
theorem isStrip_sub {ν μ : Fin n → ℤ} {b : ℕ} (h : IsStrip ν μ b) (L : ℤ) :
    IsStrip (fun a => ν a - L) (fun a => μ a - L) b := by
  refine ⟨fun a => by have := h.1 a; linarith, fun a a' haa => by have := h.2.1 a a' haa; linarith, ?_⟩
  have := h.2.2
  simp only [Finset.sum_sub_distrib]
  linarith

/-- **A shift moves the column heights.** -/
theorem colH_sub (ν : Fin n → ℤ) (L c : ℤ) : colH (fun a => ν a - L) c = colH ν (c + L) := by
  unfold colH
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and]
  omega

/-- **The extended weights in the prefix.** -/
theorem xmu_le (μ : ℕ → Fin n → ℤ) {i : ℕ} {μ₀ : Fin n → ℤ} (hμ : μ i = μ₀) (L : ℤ) {j : ℕ} (hj : j ≤ n)
    (a : Fin n) : xmu i μ μ₀ L j a = if n - j ≤ a.val then μ₀ a - L else 0 := by
  unfold xmu
  by_cases h1 : j < n
  · simp only [h1, ite_true]
  · have : j = n := by omega
    subst this
    simp [hμ]

/-- **The extended weights after the prefix.** -/
theorem xmu_ge (μ : ℕ → Fin n → ℤ) (i : ℕ) (μ₀ : Fin n → ℤ) (L : ℤ) (u : ℕ) :
    xmu i μ μ₀ L (n + u) = fun a => μ (i + u) a - L := by
  funext a
  simp [xmu]

/-- **The extended path** of a Pieri path through `μ_i = μ₀`, for a shift `L ≥ μ₀`. -/
def xpath (P : PieriPath n N vec B) {i : ℕ} (hi : i ≤ N) {μ₀ : Fin n → ℤ} (hμ : P.mu i = μ₀) {L : ℤ}
    (hL : ∀ a, μ₀ a ≤ L) : PieriPath n (n + (N - i)) (xvec i n vec) (xB i B μ₀ L) where
  mu := xmu i P.mu μ₀ L
  zero := by
    funext a
    rw [xmu_le P.mu hμ L (Nat.zero_le _)]
    simp [show ¬ n ≤ a.val from not_le.2 a.isLt]
  step t ht := by
    by_cases htn : t < n
    · have hv : xvec i n vec t = false := by simp [xvec, htn]
      rw [hv]
      show IsStrip _ _ _
      have hr : n - 1 - t < n := by omega
      set r : Fin n := ⟨n - 1 - t, hr⟩
      have hB : xB i B μ₀ L t = (L - μ₀ r).toNat := by simp [xB, htn, r]
      rw [hB]
      have e1 := xmu_le P.mu hμ L (show t ≤ n by omega)
      have e2 := xmu_le P.mu hμ L (show t + 1 ≤ n by omega)
      have hanti := hμ ▸ P.antitone i
      refine ⟨fun a => ?_, fun a a' haa => ?_, ?_⟩
      · rw [e1, e2]
        have := hL a
        split_ifs <;> omega
      · rw [e1, e2]
        have hle : μ₀ a' ≤ μ₀ a := hanti (Fin.le_def.2 (by omega))
        split_ifs <;> omega
      · have hdiff : ∀ a, xmu i P.mu μ₀ L t a = xmu i P.mu μ₀ L (t + 1) a +
            if a = r then -(μ₀ r - L) else 0 := fun a => by
          rw [e1, e2]
          by_cases har : a = r
          · subst har; simp [r]; omega
          · have : a.val ≠ n - 1 - t := fun h => har (Fin.ext h)
            simp only [har, ite_false, add_zero]
            split_ifs <;> first | rfl | omega
        rw [Finset.sum_congr rfl fun a _ => hdiff a, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp only [mem_univ, ite_true]
        have := hL r
        omega
    · obtain ⟨u, rfl⟩ : ∃ u, t = n + u := ⟨t - n, by omega⟩
      have hv : xvec i n vec (n + u) = vec (i + u) := by simp [xvec]
      have hB : xB i B μ₀ L (n + u) = B (i + u) := by simp [xB]
      rw [hv, hB, show n + u + 1 = n + (u + 1) by omega]
      show IsStep _ _ (xmu i P.mu μ₀ L (n + u)) (xmu i P.mu μ₀ L (n + (u + 1)))
      rw [xmu_ge, xmu_ge, show i + (u + 1) = i + u + 1 by omega]
      have hs := P.step (i + u) (by omega)
      unfold IsStep at hs ⊢
      split_ifs at hs ⊢
      · exact isStrip_sub hs L
      · exact isStrip_sub hs L
  stop t ht := by
    obtain ⟨u, rfl⟩ : ∃ u, t = n + u := ⟨t - n, by omega⟩
    rw [xmu_ge, xmu_ge, P.stop (i + u) (by omega), P.stop (i + (N - i)) (by omega)]

/-- **The extended filling**: the columns of `I` shifted by `L`. -/
def xfill (I : ℤ → Finset (Fin n)) (L : ℤ) : ℤ → Finset (Fin n) := colSet fun c' => colSet I (c' + L)

/-- **The extended filling is standard.** -/
theorem isStdFilling_xfill (μ : ℕ → Fin n → ℤ) (i : ℕ) (μ₀ : Fin n → ℤ) {L : ℤ} {I : ℤ → Finset (Fin n)}
    (hI : IsStdFilling (μ N) I) (hi : i ≤ N) :
    IsStdFilling (xmu i μ μ₀ L (n + (N - i))) (xfill I L) := by
  unfold IsStdFilling xfill
  rw [colSet_colSet, xmu_ge, Nat.add_sub_cancel' hi]
  refine ⟨fun c' => ?_, fun c' t => ?_⟩
  · rw [hI.1 (c' + L), colH_sub]
  · beta_reduce
    rw [show c' + 1 + L = c' + L + 1 by ring]
    exact hI.2 (c' + L) t

/-- **The dual steps of the extended path after the prefix** are those of the path, shifted. -/
theorem dstep_xmu (μ : ℕ → Fin n → ℤ) (i : ℕ) (μ₀ : Fin n → ℤ) (L c' : ℤ) (u : ℕ) :
    dstep (xmu i μ μ₀ L) c' (n + u) = dstep μ (c' + L) (i + u) := by
  unfold dstep
  rw [show n + u + 1 = n + (u + 1) by omega, xmu_ge, xmu_ge, colH_sub, colH_sub,
    show i + (u + 1) = i + u + 1 by omega]

/-- **The extended weights in the prefix are `≤ 0`.** -/
theorem xmu_nonpos (μ : ℕ → Fin n → ℤ) {i : ℕ} {μ₀ : Fin n → ℤ} (hμ : μ i = μ₀) {L : ℤ} (hL : ∀ a, μ₀ a ≤ L)
    {j : ℕ} (hj : j ≤ n) (a : Fin n) : xmu i μ μ₀ L j a ≤ 0 := by
  rw [xmu_le μ hμ L hj]
  split_ifs
  · have := hL a; omega
  · exact le_rfl

/-- **The columns `c' ≥ 1` of the extended prefix keep their initial state.** -/
theorem xprefix_pos {Λ : Type*} [CommRing Λ] (y : ℕ → Fin n → Λ) (μ : ℕ → Fin n → ℤ) {i : ℕ} {μ₀ : Fin n → ℤ}
    (hμ : μ i = μ₀) {L : ℤ} (hL : ∀ a, μ₀ a ≤ L) {c' : ℤ} (hc : 1 ≤ c') (S0 : Finset (Fin n) → Λ) :
    ∀ j ≤ n, run y (dstep (xmu i μ μ₀ L) c') S0 j = S0 := by
  have h0 : ∀ j ≤ n, colH (xmu i μ μ₀ L j) c' = 0 := fun j hj => by
    unfold colH
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ ha
    have := xmu_nonpos μ hμ hL hj a
    omega
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [run_succ, ih (by omega)]
    have hst : dstep (xmu i μ μ₀ L) c' j = .keep := by
      unfold dstep
      rw [h0 j (by omega), h0 (j + 1) hj]
      simp
    rw [hst]
    rfl

/-- **The rows of the extended prefix**: the row `r` is the letter `n − 1 − r`. -/
def Zx (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) R) :=
  Matrix.of fun r b => X (n - 1 - r.val, b)

/-- **The columns `c' ≤ 0` of the extended prefix**: the state after the `n` covector letters is `±` the wedge of the
rows `Tset` of `Zx`. -/
theorem xprefix_neg (R : Type*) [CommRing R] (μ : ℕ → Fin n → ℤ) {i : ℕ} {μ₀ : Fin n → ℤ} (hμ : μ i = μ₀)
    (hanti : Antitone μ₀) (L : ℤ) {c' : ℤ} (hc : c' ≤ 0) :
    ∃ ε : MvPolynomial (ℕ × Fin n) R, ε * ε = 1 ∧ ∀ K,
      run (fun t a => X (t, a)) (dstep (xmu i μ μ₀ L) c') st0 n K = ε * W (Zx R n) (Tset (xmu i μ μ₀ L n) c') K := by
  classical
  set Sj : ℕ → Finset (Fin n) := fun j => univ.filter fun a : Fin n => n - j ≤ a.val ∧ μ₀ a - L < c'
  have key : ∀ j ≤ n, ∃ ε : MvPolynomial (ℕ × Fin n) R, ε * ε = 1 ∧ ∀ K,
      run (fun t a => X (t, a)) (dstep (xmu i μ μ₀ L) c') st0 j K = ε * W (Zx R n) (Sj j) K := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨1, one_mul 1, fun K => ?_⟩
      have : Sj 0 = ∅ := by
        ext a; simp only [Sj, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
        intro h; exact absurd a.isLt (by omega)
      rw [this, W_empty, one_mul]; rfl
    | succ j ih =>
      intro hj
      obtain ⟨ε, hε, hrun⟩ := ih (by omega)
      obtain ⟨r, hrv⟩ : ∃ r : Fin n, r.val = n - 1 - j := ⟨⟨n - 1 - j, by omega⟩, rfl⟩
      have e1 := xmu_le μ hμ L (show j ≤ n by omega)
      have e2 := xmu_le μ hμ L hj
      have hother : ∀ a, a ≠ r → xmu i μ μ₀ L (j + 1) a = xmu i μ μ₀ L j a := fun a har => by
        rw [e1, e2]
        have : a.val ≠ n - 1 - j := fun h => har (Fin.ext (h.trans hrv.symm))
        split_ifs <;> first | rfl | omega
      have hr1 : xmu i μ μ₀ L (j + 1) r = μ₀ r - L := by
        rw [e2, ite_eq_left_iff.2 fun h => absurd (by omega) h]
      have hr0 : xmu i μ μ₀ L j r = 0 := by
        rw [e1, ite_eq_right_iff.2 fun h => absurd h (by omega)]
      have hrow : (fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) = Zx R n r := by
        funext b; simp only [Zx, Matrix.of_apply]; congr 2; omega
      have hrS : r ∉ Sj j := by simp [Sj]; omega
      rw [run_succ]
      by_cases hlt : μ₀ r - L < c'
      · have hdrop : colH (xmu i μ μ₀ L (j + 1)) c' < colH (xmu i μ μ₀ L j) c' := by
          unfold colH
          apply Finset.card_lt_card
          refine ⟨fun a ha => ?_, fun hsub => ?_⟩
          · simp only [mem_filter, mem_univ, true_and] at ha ⊢
            by_cases har : a = r
            · rw [har, hr0]; exact hc
            · rwa [← hother a har]
          · have := hsub (show r ∈ univ.filter fun a => c' ≤ xmu i μ μ₀ L j a by simp [hr0, hc])
            simp only [mem_filter, mem_univ, true_and, hr1] at this
            omega
        have hst : dstep (xmu i μ μ₀ L) c' j = .wed := by unfold dstep; simp [hdrop]
        have hS : Sj (j + 1) = insert r (Sj j) := by
          ext a
          simp only [Sj, mem_filter, mem_univ, true_and, mem_insert]
          by_cases har : a = r
          · subst har; simp only [true_or, iff_true]; exact ⟨by omega, hlt⟩
          · have : a.val ≠ n - 1 - j := fun h => har (Fin.ext (h.trans hrv.symm))
            simp only [har, false_or]
            constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
        refine ⟨ε * sg r (insert r (Sj j)), ?_, fun K => ?_⟩
        · have := sg_mul_self (R := MvPolynomial (ℕ × Fin n) R) r (insert r (Sj j))
          linear_combination (sg r (insert r (Sj j)) * sg r (insert r (Sj j))) * hε + this
        · rw [hst]
          simp only [Step.app]
          rw [show run (fun t a => X (t, a)) (dstep (xmu i μ μ₀ L) c') st0 j =
            fun K => ε * W (Zx R n) (Sj j) K from funext hrun, wedge_smul, hrow,
            wedge_W_notMem _ _ hrS, hS]
          ring
      · have hkeep : colH (xmu i μ μ₀ L (j + 1)) c' = colH (xmu i μ μ₀ L j) c' := by
          unfold colH
          congr 1
          ext a
          simp only [mem_filter, mem_univ, true_and]
          by_cases har : a = r
          · rw [har, hr0, hr1]; constructor <;> intro <;> omega
          · rw [hother a har]
        have hst : dstep (xmu i μ μ₀ L) c' j = .keep := by unfold dstep; simp [hkeep]
        have hS : Sj (j + 1) = Sj j := by
          ext a
          simp only [Sj, mem_filter, mem_univ, true_and]
          by_cases har : a = r
          · subst har; constructor <;> rintro ⟨_, h2⟩ <;> omega
          · have : a.val ≠ n - 1 - j := fun h => har (Fin.ext (h.trans hrv.symm))
            constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
        refine ⟨ε, hε, fun K => ?_⟩
        rw [hst, hS]
        exact hrun K
  obtain ⟨ε, hε, h⟩ := key n le_rfl
  refine ⟨ε, hε, fun K => ?_⟩
  rw [h K]
  congr 2
  ext a
  have hxn : xmu i μ μ₀ L n = fun a => μ₀ a - L := funext fun a => by rw [xmu_le μ hμ L le_rfl]; simp
  have hanti' : Antitone (fun a => μ₀ a - L) := fun a b hab => by have := hanti hab; simp only; omega
  rw [hxn]
  simp only [Sj, Tset, mem_filter, mem_univ, true_and, mem_compl, Nat.sub_self, zero_le]
  constructor
  · intro h1 h2
    have := colH_le_of_lt hanti' (show (fun a => μ₀ a - L) a < c' from h1)
    omega
  · intro h1
    by_contra hne
    have := le_colH hanti' (show c' ≤ (fun a => μ₀ a - L) a by simp only; omega)
    exact h1 (by omega)

end Ext

/-! ## The substitution of the extended word -/

section XSub

variable {R : Type*} [CommRing R] {n : ℕ}

variable (R n) in
/-- **The substitution of the extended word**: the letter `j < n` becomes the column `n − 1 − j` of `g`, the letter
`n + u` the letter `i + u`. -/
def xsub (i : ℕ) : MvPolynomial (ℕ × Fin n) R →+* SymbolData.GenCoeff ℕ R n :=
  eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun v =>
    if h : v.1 < n then MvPolynomial.C (X (v.2, ⟨n - 1 - v.1, by omega⟩)) else X (i + (v.1 - n), v.2)

/-- **The later letters are shifted.** -/
theorem xsub_X_ge (i u : ℕ) (b : Fin n) : xsub R n i (X (n + u, b)) = X (i + u, b) := by
  simp [xsub]

/-- **Constants are fixed.** -/
theorem xsub_C (i : ℕ) (r : R) : xsub R n i (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  simp [xsub]

/-- **The rows of the extended prefix become the rows of `gᵀ`.** -/
theorem xsub_Zx (i : ℕ) (r b : Fin n) : xsub R n i (Zx R n r b) = Aw false r b := by
  have hr : n - 1 - r.val < n := by omega
  simp only [Zx, Matrix.of_apply, xsub, coe_eval₂Hom, eval₂_X, hr, dite_true, Aw, Bool.false_eq_true, ite_false,
    genMat]
  congr 3
  ext; simp; omega

/-- **The wedges of the rows of the extended prefix become wedges of the rows of `gᵀ`.** -/
theorem xsub_W (i : ℕ) (T K : Finset (Fin n)) : xsub R n i (W (Zx R n) T K) = W (Aw (R := R) false) T K := by
  rw [map_W (xsub R n i)]
  congr 1
  refine Matrix.ext fun r b => ?_
  rw [Matrix.map_apply]
  exact xsub_Zx (R := R) i r b

/-- **The substitution is injective**: it is a renaming followed by `R[x ⊕ g] ≅ R[g][x]`. -/
theorem xsub_injective (i : ℕ) : Function.Injective (xsub R n i) := by
  classical
  let f : ℕ × Fin n → (ℕ × Fin n) ⊕ (Fin n × Fin n) := fun v =>
    if h : v.1 < n then Sum.inr (v.2, ⟨n - 1 - v.1, by omega⟩) else Sum.inl (i + (v.1 - n), v.2)
  have hf : Function.Injective f := by
    rintro ⟨j, b⟩ ⟨j', b'⟩ h
    simp only [f] at h
    split_ifs at h with h1 h2 h2 <;>
      simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, Fin.mk.injEq] at h <;>
      ext <;> simp <;> omega
  have e : xsub R n i = (sumRingEquiv R (ℕ × Fin n) (Fin n × Fin n)).toRingHom.comp (rename f).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun v => ?_
    · simp [xsub, sumRingEquiv_C]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rename_X, xsub, coe_eval₂Hom, eval₂_X, f]
      split_ifs
      · rw [sumRingEquiv_X_inr]
      · rw [sumRingEquiv_X_inl]
  rw [e]
  exact (sumRingEquiv R (ℕ × Fin n) (Fin n × Fin n)).injective.comp (rename_injective f hf)

/-- **The substitution is `R`-linear.** -/
theorem xsub_smul (i : ℕ) (r : R) (F : MvPolynomial (ℕ × Fin n) R) : xsub R n i (r • F) = r • xsub R n i F := by
  rw [smul_eq_C_mul, map_mul, xsub_C, Algebra.smul_def, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

/-- **Runs from a stage commute with ring homomorphisms and shifts.** -/
theorem runFrom_map_shift {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] (f : Λ →+* Λ') (y : ℕ → Fin n → Λ)
    (y' : ℕ → Fin n → Λ') (st st' : ℕ → Step) (a b : ℕ) (S : Finset (Fin n) → Λ)
    (hy : ∀ u d, f (y (a + u) d) = y' (b + u) d) (hst : ∀ u, st (a + u) = st' (b + u)) :
    ∀ k J, f (runFrom y st a S k J) = runFrom y' st' b (fun J => f (S J)) k J := by
  intro k
  induction k with
  | zero => intro J; rfl
  | succ k ih =>
    intro J
    rw [runFrom, runFrom, map_app, hst k]
    rw [show (fun d => f (y (a + k) d)) = y' (b + k) from funext (hy k),
      show (fun J => f (runFrom y st a S k J)) = runFrom y' st' b (fun J => f (S J)) k from funext ih]

end XSub

/-! ## The top component of a column through the extended word -/

section ColIdentity

variable {R : Type*} [CommRing R] {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **The wedge of all rows** is a multiple of `[univ]`. -/
theorem W_univ {Λ : Type*} [CommRing Λ] (A : Matrix (Fin n) (Fin n) Λ) (K : Finset (Fin n)) :
    W A univ K = W A univ univ * (if K = univ then 1 else 0) := by
  by_cases hK : K = univ
  · rw [hK]; simp
  · rw [W_isDeg _ univ K fun h => hK (Finset.eq_univ_of_card K (by rw [h]; simp))]
    simp [hK]

/-- **Hodge signs pass through ring homomorphisms.** -/
theorem map_hsg {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] (f : Λ →+* Λ') (J : Finset (Fin n)) :
    f (hsg J) = hsg J := by
  simp [hsg]

/-- **The sign of the dual form squares to one.** -/
theorem dsgn_sq {Λ : Type*} [CommRing Λ] (c : ℤ) (K : Finset (Fin n)) :
    (if 1 ≤ c then hsg Kᶜ * hsg (univ : Finset (Fin n)) else 1 : Λ) *
      (if 1 ≤ c then hsg Kᶜ * hsg (univ : Finset (Fin n)) else 1) = 1 := by
  split_ifs
  · linear_combination (hsg (univ : Finset (Fin n)) * hsg univ) * hsg_mul_self (Λ := Λ) Kᶜ +
      hsg_mul_self (Λ := Λ) (univ : Finset (Fin n))
  · ring

/-- **Signs have weight `0`.** -/
theorem isWH_hsgs (w : ℕ × Fin n → Fin n → ℤ) (c : ℤ) (K : Finset (Fin n)) :
    IsWeightedHomogeneous w (if 1 ≤ c then hsg Kᶜ * hsg (univ : Finset (Fin n)) else 1 :
      SymbolData.GenCoeff ℕ R n) 0 := by
  have h : ∀ J : Finset (Fin n), IsWeightedHomogeneous w (hsg J : SymbolData.GenCoeff ℕ R n) 0 := fun J => by
    rw [hsg, show ((-1 : SymbolData.GenCoeff ℕ R n)) = MvPolynomial.C (-1) from by simp, ← map_pow]
    exact isWeightedHomogeneous_C w _
  split_ifs
  · simpa using (h Kᶜ).mul (h univ)
  · exact isWeightedHomogeneous_one _ _

/-- **The dual coordinate of a column of a filling** is the complement of its column set. -/
theorem dualCoord (I : ℤ → Finset (Fin n)) (c : ℤ) : (if 1 ≤ c then (I c)ᶜ else I c) = (colSet I c)ᶜ := by
  unfold colSet; split_ifs <;> simp

/-- **`Φ_c` through the extended word**: `Φ_c = η·xsub(D'_{c − L})` with `η = W_{gᵀ}(univ)(univ)` for `c > L` and a
sign otherwise. -/
theorem xcol_phi (P : PieriPath n N vec B) {i : ℕ} {μ₀ : Fin n → ℤ} (hμ : P.mu i = μ₀) (hanti : Antitone μ₀)
    {L : ℤ} (hL : ∀ a, μ₀ a ≤ L) (c : ℤ) :
    ∃ ε : SymbolData.GenCoeff ℕ R n, ε * ε = 1 ∧ ∀ K,
      runFrom (Yv (R := R)) (dstep P.mu c) i (W (Aw false) (Tset μ₀ c)) (N - i) K =
        (if L + 1 ≤ c then W (Aw (R := R) false) univ univ else ε) *
          xsub R n i (run (fun t a => X (t, a)) (dstep (xmu i P.mu μ₀ L) (c - L)) (dinit (c - L)) (n + (N - i)) K) := by
  have hsplit : ∀ K, xsub R n i (run (fun t a => X (t, a)) (dstep (xmu i P.mu μ₀ L) (c - L)) (dinit (c - L))
      (n + (N - i)) K) = runFrom (Yv (R := R)) (dstep P.mu c) i (fun K => xsub R n i
        (run (fun t a => X (t, a)) (dstep (xmu i P.mu μ₀ L) (c - L)) (dinit (c - L)) n K)) (N - i) K := fun K => by
    have hy : ∀ u d, xsub R n i ((fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) R)) (n + u) d) =
        Yv (R := R) (i + u) d := fun u d => xsub_X_ge i u d
    have hst : ∀ u, dstep (xmu i P.mu μ₀ L) (c - L) (n + u) = dstep P.mu c (i + u) := fun u => by
      rw [dstep_xmu, sub_add_cancel]
    rw [run_add]
    exact runFrom_map_shift (xsub R n i) (fun t a => X (t, a)) (Yv (R := R)) (dstep (xmu i P.mu μ₀ L) (c - L))
      (dstep P.mu c) n i (run (fun t a => X (t, a)) (dstep (xmu i P.mu μ₀ L) (c - L)) (dinit (c - L)) n) hy hst
      (N - i) K
  by_cases hc : L + 1 ≤ c
  · refine ⟨1, one_mul 1, fun K => ?_⟩
    have hc' : 1 ≤ c - L := by omega
    simp only [hc, ite_true]
    rw [hsplit, xprefix_pos _ P.mu hμ hL hc' _ n le_rfl]
    have hT : Tset μ₀ c = univ := by
      unfold Tset
      rw [compl_eq_univ_iff, filter_eq_empty_iff]
      intro a _ ha
      have : colH μ₀ c = 0 := by
        unfold colH
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro b _ hb
        have := hL b; omega
      omega
    have hW : W (Aw (R := R) false) (Tset μ₀ c) = fun K => W (Aw (R := R) false) univ univ *
        xsub R n i (dinit (c - L) K : MvPolynomial (ℕ × Fin n) R) := by
      funext K
      rw [hT, W_univ]
      simp only [dinit, hc', ite_true]
      split_ifs <;> simp
    rw [hW, runFrom_smul]
  · have hc' : ¬ 1 ≤ c - L := by omega
    obtain ⟨ε, hε, hrun⟩ := xprefix_neg R P.mu hμ hanti L (show c - L ≤ 0 by omega)
    have hdi : (dinit (c - L) : Finset (Fin n) → MvPolynomial (ℕ × Fin n) R) = st0 := by simp [dinit, hc']
    have hT : Tset (xmu i P.mu μ₀ L n) (c - L) = Tset μ₀ c := by
      have hxn : xmu i P.mu μ₀ L n = fun a => μ₀ a - L := funext fun a => by rw [xmu_le P.mu hμ L le_rfl]; simp
      unfold Tset; rw [hxn, colH_sub, sub_add_cancel]
    refine ⟨xsub R n i ε, by rw [← map_mul, hε, map_one], fun K => ?_⟩
    simp only [hc, ite_false]
    rw [hsplit, hdi]
    have hx : (fun K => xsub R n i (run (fun t a => X (t, a)) (dstep (xmu i P.mu μ₀ L) (c - L)) st0 n K)) =
        fun K => xsub R n i ε * W (Aw false) (Tset μ₀ c) K := by
      funext K; rw [hrun K, map_mul, xsub_W, hT]
    rw [hx, runFrom_smul, ← mul_assoc, ← map_mul, hε, map_one, one_mul]

/-- **The column set of the canonical filling.** -/
theorem colSet_canFill (lam : Fin n → ℤ) (c : ℤ) :
    (colSet (canFill lam) c)ᶜ = Tset lam c := by
  unfold canFill Tset
  rw [colSet_colSet]

/-- **The coefficient embedding of a run.** -/
theorem mapC_run (st : ℕ → Step) (c : ℤ) (t : ℕ) (J : Finset (Fin n)) :
    MvPolynomial.map MvPolynomial.C (run (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) R)) st (dinit c) t J) =
      run (Yv (R := R)) st (dinit c) t J := by
  rw [map_run]
  congr 1
  · funext t a; simp
  · funext J; unfold dinit; split_ifs <;> simp [st0]

/-- **(E2 through the extended word) The top component of a column**: up to a sign `s`,
`κ_c·[gtr K_c(N)(I(c))]_{τ_c} = det(g)^{#con}·K_c(i)(can)·η_c·xsub(K'_{c − L}(I'))`, with `K'` the column states of
the extended path, `I'` the extended filling and `η_c = W_{gᵀ}(univ)(univ)` for `c > L`, `1` otherwise. -/
theorem col_identity (P : PieriPath n N vec B) {i : ℕ} (hi : i ≤ N) {μ₀ : Fin n → ℤ} (hμ : P.mu i = μ₀)
    (hanti : Antitone μ₀) {L : ℤ} (hL : ∀ a, μ₀ a ≤ L) (I : ℤ → Finset (Fin n)) (c : ℤ) :
    ∃ s : SymbolData.GenCoeff ℕ R n, s * s = 1 ∧
      kap c * weightedHomogeneousComponent (twWt vec (Set.Iio i)) (tau μ₀ c)
        (gtr vec (Set.Iio i) (colK R P.mu c N (I c))) =
      s * MvPolynomial.C (genMat R n).det ^ ncon (dstep P.mu c) i *
        MvPolynomial.map MvPolynomial.C (colK R P.mu c i (canFill μ₀ c)) *
        (if L + 1 ≤ c then W (Aw (R := R) false) univ univ else 1) *
        xsub R n i (colK R (xmu i P.mu μ₀ L) (c - L) (n + (N - i)) (xfill I L (c - L))) := by
  subst hμ
  set w := twWt (n := n) vec (Set.Iio i)
  set J : Finset (Fin n) := if 1 ≤ c then (I c)ᶜ else I c with hJdef
  have hJ : J = (colSet I c)ᶜ := dualCoord I c
  -- the column in dual form
  have hK : colK R P.mu c N (I c) = (if 1 ≤ c then hsg (I c)ᶜ * hsg (univ : Finset (Fin n)) else 1) *
      run (fun t a => X (t, a)) (dstep P.mu c) (dinit c) N J := by
    rw [colK, colSt_one_eq_run, colK_eq_dual]
  have hgs : gtr (R := R) (n := n) vec (Set.Iio i)
      (if 1 ≤ c then hsg (I c)ᶜ * hsg (univ : Finset (Fin n)) else 1) =
      (if 1 ≤ c then hsg (I c)ᶜ * hsg (univ : Finset (Fin n)) else 1 : SymbolData.GenCoeff ℕ R n) := by
    split_ifs <;> simp [map_hsg]
  -- the prefix factor
  have hI0 := colK_eq_dual (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) R)) P.mu c i (canFill (P.mu i) c)
  rw [dualCoord, colSet_canFill] at hI0
  have hpre : run (Yv (R := R)) (dstep P.mu c) (dinit c) i (Tset (P.mu i) c) =
      MvPolynomial.map MvPolynomial.C (if 1 ≤ c then hsg (canFill (P.mu i) c)ᶜ * hsg (univ : Finset (Fin n)) else 1) *
        MvPolynomial.map MvPolynomial.C (colK R P.mu c i (canFill (P.mu i) c)) := by
    rw [← mapC_run, ← map_mul, colK, colSt_one_eq_run, hI0, ← mul_assoc, dsgn_sq, one_mul]
  -- the extended factor
  obtain ⟨ε, hε, hΦ⟩ := xcol_phi (R := R) P rfl hanti hL c
  have hX0 := colK_eq_dual (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) R)) (xmu i P.mu (P.mu i) L) (c - L)
    (n + (N - i)) (xfill I L (c - L))
  rw [dualCoord, show colSet (xfill I L) (c - L) = colSet I c by
    unfold xfill; rw [colSet_colSet, sub_add_cancel], ← hJ] at hX0
  have hext : run (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin n) R)) (dstep (xmu i P.mu (P.mu i) L) (c - L))
      (dinit (c - L)) (n + (N - i)) J =
      (if 1 ≤ c - L then hsg (xfill I L (c - L))ᶜ * hsg (univ : Finset (Fin n)) else 1) *
        colK R (xmu i P.mu (P.mu i) L) (c - L) (n + (N - i)) (xfill I L (c - L)) := by
    rw [colK, colSt_one_eq_run, hX0, ← mul_assoc, dsgn_sq, one_mul]
  set sG : SymbolData.GenCoeff ℕ R n := if 1 ≤ c then hsg (I c)ᶜ * hsg (univ : Finset (Fin n)) else 1
  set sI : MvPolynomial (ℕ × Fin n) R := if 1 ≤ c then hsg (canFill (P.mu i) c)ᶜ * hsg (univ : Finset (Fin n)) else 1
  set sX : MvPolynomial (ℕ × Fin n) R := if 1 ≤ c - L then hsg (xfill I L (c - L))ᶜ * hsg (univ : Finset (Fin n))
    else 1
  refine ⟨sG * MvPolynomial.map MvPolynomial.C sI * (if L + 1 ≤ c then 1 else ε) * xsub R n i sX, ?_, ?_⟩
  · set mI : SymbolData.GenCoeff ℕ R n := MvPolynomial.map MvPolynomial.C sI
    set e4 : SymbolData.GenCoeff ℕ R n := if L + 1 ≤ c then 1 else ε
    set mX : SymbolData.GenCoeff ℕ R n := xsub R n i sX
    have h1 : sG * sG = 1 := dsgn_sq c (I c)
    have h2 : mI * mI = 1 := by simp only [mI]; rw [← map_mul, dsgn_sq, map_one]
    have h3 : mX * mX = 1 := by simp only [mX]; rw [← map_mul, dsgn_sq, map_one]
    have h4 : e4 * e4 = 1 := by
      simp only [e4]
      split_ifs
      · ring
      · exact hε
    linear_combination (mI * mI * e4 * e4 * mX * mX) * h1 + (e4 * e4 * mX * mX) * h2 + (mX * mX) * h4 + h3
  · rw [hK, map_mul, hgs, comp_mul_of_isWH0 w (isWH_hsgs w c (I c)), mul_left_comm, col_top P hi c J, hpre,
      hΦ J, hext, map_mul]
    by_cases hcL : L + 1 ≤ c
    · simp only [hcL, ite_true]; ring
    · simp only [hcL, ite_false]; ring

/-- **The column range grows with the stage.** -/
theorem colRange_mono (μ : ℕ → Fin n → ℤ) {i N : ℕ} (hi : i ≤ N) : colRange μ i ⊆ colRange μ N := by
  have h : ∑ t ∈ range (i + 1), ∑ a, |μ t a| ≤ ∑ t ∈ range (N + 1), ∑ a, |μ t a| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun t _ _ => Finset.sum_nonneg fun a _ => abs_nonneg _
  intro c hc
  simp only [colRange, mem_Icc] at hc ⊢
  constructor <;> linarith [hc.1, hc.2]

/-- **The top component of a path polynomial through the extended word**: up to a sign `s`,
`(Π_c κ_c)·[gtr Ψ(P, I)]_{μ₀} = s·det(g)^e·Ψ(P|_{≤i}, can)·(Π_{c > L} κ')·xsub(Ψ'(P', I'))`, over a window `[−T, T]`
containing the column ranges of the path and (shifted by `L`) of the extended path. -/
theorem top_identity (P : PieriPath n N vec B) {I : ℤ → Finset (Fin n)} (hI : IsStdFilling (P.mu N) I)
    {i : ℕ} (hi : i ≤ N) {μ₀ : Fin n → ℤ} (hμ : P.mu i = μ₀) (hanti : Antitone μ₀) {L : ℤ} (hL : ∀ a, μ₀ a ≤ L)
    {T : ℤ} (hT1 : colRange P.mu N ⊆ Icc (-T) T)
    (hT2 : colRange (xmu i P.mu μ₀ L) (n + (N - i)) ⊆ Icc (-T - L) (T - L)) :
    ∃ s : SymbolData.GenCoeff ℕ R n, s * s = 1 ∧
      (∏ c ∈ Icc (-T) T, kap c) * gcomp vec (Set.Iio i) μ₀ (pathPoly R P.mu N I) =
        s * MvPolynomial.C (genMat R n).det ^ (∑ c ∈ Icc (-T) T, ncon (dstep P.mu c) i) *
          MvPolynomial.map MvPolynomial.C (pathPoly R P.mu i (canFill μ₀)) *
          (∏ c ∈ Icc (-T) T, if L + 1 ≤ c then W (Aw (R := R) false) univ univ else 1) *
          xsub R n i (pathPoly R (xmu i P.mu μ₀ L) (n + (N - i)) (xfill I L)) := by
  classical
  choose s hs heq using fun c => col_identity (R := R) P hi hμ hanti hL I c
  refine ⟨∏ c ∈ Icc (-T) T, s c, by rw [← Finset.prod_mul_distrib, Finset.prod_eq_one fun c _ => hs c], ?_⟩
  have hbound : ∀ a, |μ₀ a| ≤ T := fun a => by
    have h := abs_le_colRange P.mu hi a
    rw [hμ] at h
    have hm : (∑ t ∈ range (N + 1), ∑ a, |P.mu t a|) ∈ colRange P.mu N := by
      simp only [colRange, mem_Icc]
      constructor
      · linarith [Finset.sum_nonneg fun t (_ : t ∈ range (N + 1)) =>
          Finset.sum_nonneg fun a (_ : a ∈ (univ : Finset (Fin n))) => abs_nonneg (P.mu t a)]
      · exact le_rfl
    have := (mem_Icc.1 (hT1 hm)).2
    linarith
  have hgc : gcomp vec (Set.Iio i) μ₀ (pathPoly R P.mu N I) =
      ∏ c ∈ Icc (-T) T, weightedHomogeneousComponent (twWt vec (Set.Iio i)) (tau μ₀ c)
        (gtr vec (Set.Iio i) (colK R P.mu c N (I c))) := by
    rw [gcomp, pathPoly_eq_prod P.zero hI hT1, map_prod]
    conv_lhs => rw [← sum_tau_win μ₀ hanti hbound]
    refine top_comp_prod _ _ _ _ fun c _ => ?_
    have := colK_wtIn (R := R) P hi c (I c)
    rwa [hμ] at this
  have hpre : pathPoly R P.mu i (canFill μ₀) = ∏ c ∈ Icc (-T) T, colK R P.mu c i (canFill μ₀ c) :=
    pathPoly_eq_prod P.zero (hμ ▸ isStdFilling_canFill (P.mu i)) ((colRange_mono P.mu hi).trans hT1)
  have hx : pathPoly R (xmu i P.mu μ₀ L) (n + (N - i)) (xfill I L) =
      ∏ c ∈ Icc (-T) T, colK R (xmu i P.mu μ₀ L) (c - L) (n + (N - i)) (xfill I L (c - L)) := by
    rw [pathPoly_eq_prod (μ := xmu i P.mu μ₀ L) (xpath P hi hμ hL).zero (isStdFilling_xfill P.mu i μ₀ hI hi) hT2]
    refine Finset.prod_nbij' (fun c => c + L) (fun c => c - L) (fun c hc => ?_) (fun c hc => ?_)
      (fun c _ => by ring) (fun c _ => by ring) (fun c _ => by rw [add_sub_cancel_right])
    · simp only [mem_Icc] at hc ⊢; constructor <;> linarith [hc.1, hc.2]
    · simp only [mem_Icc] at hc ⊢; constructor <;> linarith [hc.1, hc.2]
  rw [hgc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun c _ => heq c, hpre, hx, map_prod, map_prod,
    ← Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_mul_distrib]

end ColIdentity

/-! ## Products of independent families in disjoint variables -/

section Tensor

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The coefficient of a product in disjoint variables**: letters `< i` in `p`, letters `≥ i` in `q`. -/
theorem coeff_mul_disjoint {i : ℕ} {p q : SymbolData.GenCoeff ℕ R n}
    (hp : ∀ m ∈ p.support, ∀ v ∈ m.support, v.1 < i) (hq : ∀ m ∈ q.support, ∀ v ∈ m.support, i ≤ v.1)
    {m1 m2 : ℕ × Fin n →₀ ℕ} (h1 : ∀ v ∈ m1.support, v.1 < i) (h2 : ∀ v ∈ m2.support, i ≤ v.1) :
    (p * q).coeff (m1 + m2) = p.coeff m1 * q.coeff m2 := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (m1, m2)]
  · intro x hx hne
    by_cases hp0 : p.coeff x.1 = 0
    · rw [hp0, zero_mul]
    by_cases hq0 : q.coeff x.2 = 0
    · rw [hq0, mul_zero]
    exfalso
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hpx := hp x.1 (mem_support_iff.2 hp0)
    have hqx := hq x.2 (mem_support_iff.2 hq0)
    have e : ∀ v : ℕ × Fin n, x.1 v + x.2 v = m1 v + m2 v := fun v => by
      have := DFunLike.congr_fun hx' v
      simpa only [Finsupp.add_apply] using this
    apply hne
    have e1 : x.1 = m1 := by
      ext v
      by_cases hv : v.1 < i
      · have a1 : x.2 v = 0 := by
          by_contra h; have := hqx v (Finsupp.mem_support_iff.2 h); omega
        have a2 : m2 v = 0 := by
          by_contra h; have := h2 v (Finsupp.mem_support_iff.2 h); omega
        have := e v; omega
      · have a1 : x.1 v = 0 := by
          by_contra h; exact hv (hpx v (Finsupp.mem_support_iff.2 h))
        have a2 : m1 v = 0 := by
          by_contra h; exact hv (h1 v (Finsupp.mem_support_iff.2 h))
        rw [a1, a2]
    have e2 : x.2 = m2 := by
      ext v
      have := e v
      rw [e1] at this
      omega
    exact Prod.ext e1 e2
  · intro h
    exact absurd ((Finset.HasAntidiagonal.mem_antidiagonal (n := m1 + m2) (a := (m1, m2))).2 rfl) h

/-- **Independent families in disjoint variables** (the tensor fact): if the `u_k` (letters `< i`) are independent
and the `V_k` have letters `≥ i`, then `Σ_k u_k·V_k = 0` forces every `V_k = 0`. -/
theorem tensor_indep {κ : Type*} [Fintype κ] {i : ℕ} (u : κ → MvPolynomial (ℕ × Fin n) R)
    (hu : LinearIndependent R u) (hsu : ∀ k, ∀ m ∈ (u k).support, ∀ v ∈ m.support, v.1 < i)
    (V : κ → SymbolData.GenCoeff ℕ R n) (hsV : ∀ k, ∀ m ∈ (V k).support, ∀ v ∈ m.support, i ≤ v.1)
    (h : ∑ k, MvPolynomial.map MvPolynomial.C (u k) * V k = 0) : ∀ k, V k = 0 := by
  classical
  have hsu' : ∀ k, ∀ m ∈ (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial (Fin n × Fin n) R) (u k)).support,
      ∀ v ∈ m.support, v.1 < i := fun k m hm => hsu k m (by
        rw [mem_support_iff, coeff_map] at hm
        rw [mem_support_iff]
        exact fun h0 => hm (by rw [h0, map_zero]))
  intro k0
  ext m2 mg
  by_cases hm2 : ∀ v ∈ m2.support, i ≤ v.1
  · let r : κ → R := fun k => ((V k).coeff m2).coeff mg
    have hr : ∑ k, r k • u k = 0 := by
      ext m1
      rw [coeff_sum]
      simp only [coeff_smul, smul_eq_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_cases hm1 : ∀ v ∈ m1.support, v.1 < i
      · have hc := congrArg (fun F : SymbolData.GenCoeff ℕ R n => (F.coeff (m1 + m2)).coeff mg) h
        simp only [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
        have hc2 : ∀ k, (((MvPolynomial.map MvPolynomial.C) (u k) * V k).coeff (m1 + m2)).coeff mg =
            (u k).coeff m1 * r k := fun k => by
          rw [coeff_mul_disjoint (hsu' k) (hsV k) hm1 hm2, coeff_map, MvPolynomial.coeff_C_mul]
        simp only [hc2] at hc
        rw [← hc]
        exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
      · obtain ⟨v, hv, hvi⟩ : ∃ v ∈ m1.support, i ≤ v.1 := by simpa using hm1
        refine Finset.sum_eq_zero fun k _ => ?_
        have : (u k).coeff m1 = 0 := by
          by_contra hne
          exact absurd (hsu k m1 (mem_support_iff.2 hne) v hv) (by omega)
        rw [this, mul_zero]
    have := (Fintype.linearIndependent_iff.1 hu) r hr k0
    simp only [r] at this
    rw [this]
    simp
  · obtain ⟨v, hv, hvi⟩ : ∃ v ∈ m2.support, v.1 < i := by simpa using hm2
    have : (V k0).coeff m2 = 0 := by
      by_contra hne
      exact absurd (hsV k0 m2 (mem_support_iff.2 hne) v hv) (by omega)
    rw [this]
    simp

end Tensor

/-! ## (E3) The top components are independent -/

section E3

variable {R : Type*} [CommRing R] {n N : ℕ} {vec : ℕ → Bool} {B : ℕ → ℕ}

/-- **A run only sees the steps of the letters read.** -/
theorem run_congr_st {Λ : Type*} [CommRing Λ] (y : ℕ → Fin n → Λ) {st st' : ℕ → Step} (S0 : Finset (Fin n) → Λ)
    {t : ℕ} (h : ∀ u < t, st u = st' u) : run y st S0 t = run y st' S0 t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, run_succ, ih fun u hu => h u (by omega), h t (by omega)]

/-- **The contraction count only sees the steps of the letters read.** -/
theorem ncon_congr {st st' : ℕ → Step} {t : ℕ} (h : ∀ u < t, st u = st' u) : ncon st t = ncon st' t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ncon, ncon, ih fun u hu => h u (by omega), h t (by omega)]

/-- **A path polynomial only sees the weights up to its length.** -/
theorem pathPoly_congr {μ μ' : ℕ → Fin n → ℤ} {i : ℕ} (h : ∀ t ≤ i, μ t = μ' t) (I : ℤ → Finset (Fin n)) :
    pathPoly R μ i I = pathPoly R μ' i I := by
  have hr : colRange μ i = colRange μ' i := by
    unfold colRange
    rw [Finset.sum_congr rfl fun t ht => by rw [h t (by simp at ht; omega)]]
  rw [pathPoly, pathPoly, hr]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [colK, colK, colSt_one_eq_run, colSt_one_eq_run, run_congr_st _ _ fun u hu => ?_]
  unfold colStep
  rw [h u (by omega), h (u + 1) (by omega)]

/-- **The truncation of a Pieri path** at `i ≤ N`. -/
def truncP (P : PieriPath n N vec B) (i : ℕ) (hi : i ≤ N) : PieriPath n i vec B where
  mu t := P.mu (min t i)
  zero := by simp [P.zero]
  step t ht := by
    rw [min_eq_left (by omega : t ≤ i), min_eq_left (by omega : t + 1 ≤ i)]
    exact P.step t (by omega)
  stop t ht := by rw [min_eq_right ht, min_self]

/-- **Pieri paths are determined by their weights.** -/
theorem PieriPath.ext' {P Q : PieriPath n N vec B} (h : P.mu = Q.mu) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- **Column systems determine fillings.** -/
theorem colSet_injective : Function.Injective (colSet : (ℤ → Finset (Fin n)) → ℤ → Finset (Fin n)) := by
  intro I J h
  rw [← colSet_colSet I, h, colSet_colSet]

/-- **A variable of `s` lies in `supported s`** (over any ring). -/
theorem X_mem_supported' {σ A : Type*} [CommRing A] {s : Set σ} {v : σ} (h : v ∈ s) :
    (X v : MvPolynomial σ A) ∈ supported A s :=
  Algebra.subset_adjoin ⟨v, h, rfl⟩

/-- **The column states only involve the letters read.** -/
theorem run_mem_supported (st : ℕ → Step) (S0 : Finset (Fin n) → MvPolynomial (ℕ × Fin n) R)
    (hS0 : ∀ J, S0 J ∈ supported R {v : ℕ × Fin n | v.1 < 0}) :
    ∀ t J, run (fun t a => X (t, a)) st S0 t J ∈ supported R {v : ℕ × Fin n | v.1 < t} := by
  intro t
  induction t with
  | zero => exact hS0
  | succ t ih =>
    intro J
    have hmono : supported R {v : ℕ × Fin n | v.1 < t} ≤ supported R {v : ℕ × Fin n | v.1 < t + 1} :=
      supported_mono fun v (hv : v.1 < t) => show v.1 < t + 1 by omega
    have hX : ∀ a, (X (t, a) : MvPolynomial (ℕ × Fin n) R) ∈ supported R {v : ℕ × Fin n | v.1 < t + 1} :=
      fun a => X_mem_supported' (show t < t + 1 by omega)
    have hsg : ∀ (a : Fin n) (K : Finset (Fin n)),
        (sg a K : MvPolynomial (ℕ × Fin n) R) ∈ supported R {v : ℕ × Fin n | v.1 < t + 1} :=
      fun a K => by
        rw [sg]
        exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) ((K.filter (a < ·)).card)
    rw [run_succ]
    cases st t
    · exact hmono (ih J)
    · exact Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hsg _ _) (hX a))
        (hmono (ih _))
    · exact Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hsg _ _) (hX a))
        (hmono (ih _))

/-- **A path polynomial only involves its letters.** -/
theorem pathPoly_supported (μ : ℕ → Fin n → ℤ) (i : ℕ) (I : ℤ → Finset (Fin n)) :
    ∀ m ∈ (pathPoly R μ i I).support, ∀ v ∈ m.support, v.1 < i := by
  have h : pathPoly R μ i I ∈ supported R {v : ℕ × Fin n | v.1 < i} := by
    refine Subalgebra.prod_mem _ fun c _ => ?_
    rw [colK, colSt_one_eq_run]
    refine run_mem_supported _ _ (fun J => ?_) i (I c)
    simp only [st0]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  intro m hm v hv
  have := mem_supported.1 h ((mem_vars_iff_mem_support v).2 ⟨m, hm, hv⟩)
  exact this

/-- **The substitution of the extended word lands in the later letters.** -/
theorem xsub_supported (i : ℕ) (F : MvPolynomial (ℕ × Fin n) R) :
    xsub R n i F ∈ supported (MvPolynomial (Fin n × Fin n) R) {v : ℕ × Fin n | i ≤ v.1} := by
  induction F using MvPolynomial.induction_on with
  | C a => rw [xsub_C]; exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p v hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp ?_
    simp only [xsub, coe_eval₂Hom, eval₂_X]
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact X_mem_supported' (show i ≤ i + (v.1 - n) by omega)

/-- **Membership in `supported` through the support.** -/
theorem support_of_supported {σ A : Type*} [CommRing A] {s : Set σ} {p : MvPolynomial σ A}
    (h : p ∈ supported A s) : ∀ m ∈ p.support, ∀ v ∈ m.support, v ∈ s := fun m hm v hv =>
  mem_supported.1 h ((mem_vars_iff_mem_support v).2 ⟨m, hm, hv⟩)

/-- **The wedge of all rows of `gᵀ` is non-zero** (it specialises to `1` at `g = 1`). -/
theorem kap_ne_zero [Nontrivial R] : W (Aw (R := R) (n := n) false) univ univ ≠ 0 := by
  classical
  have e : Aw (R := R) (n := n) false = (genMat R n).transpose.map MvPolynomial.C := by
    ext b d; simp [Aw]
  rw [e, ← map_W]
  intro h0
  set φ : MvPolynomial (Fin n × Fin n) R →+* R := MvPolynomial.eval fun p => if p.1 = p.2 then (1 : R) else 0
  have h1 := congrArg φ ((MvPolynomial.C_eq_zero).1 h0)
  rw [map_zero, map_W] at h1
  have h2 : (genMat R n).transpose.map φ = 1 := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, genMat, Matrix.of_apply, φ, eval_X, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  rw [h2, W_one, ite_eq_left_iff.2 fun h => absurd rfl h] at h1
  exact one_ne_zero h1

/-- **`κ'` is a constant.** -/
theorem W_Aw_false_eq : W (Aw (R := R) (n := n) false) univ univ =
    MvPolynomial.C (W (genMat R n).transpose univ univ) := by
  have e : Aw (R := R) (n := n) false = (genMat R n).transpose.map MvPolynomial.C := by
    ext b d; simp [Aw]
  rw [e, ← map_W]

variable (R) in
/-- **The path family is linearly independent** in the polynomial ring. -/
theorem pathFam_linearIndependent (m N : ℕ) (vec : ℕ → Bool) (B : ℕ → ℕ) :
    LinearIndependent R (pathFam R : PathIdx (m + 1) N vec B → MvPolynomial (ℕ × Fin (m + 1)) R) := by
  have h := (pathVec_linearIndependent R m N vec B).map' _ (Submodule.ker_subtype _)
  have e : (pathFam R : PathIdx (m + 1) N vec B → MvPolynomial (ℕ × Fin (m + 1)) R) =
      (weightedHomogeneousSubmodule R (LetterFock.rowW ℕ (m + 1)) (PathSpan.mdeg N B)).subtype ∘
        pathVec R m N vec B := by
    funext x; rfl
  rw [e]
  exact h

/-- **The extended index is injective on a prefix fibre.** -/
theorem ext_injective {i : ℕ} (hi : i ≤ N) {μ₀ : Fin n → ℤ} {L : ℤ} (hL : ∀ a, μ₀ a ≤ L)
    {x y : PathIdx n N vec B} (hx : x.1.mu i = μ₀) (hy : y.1.mu i = μ₀)
    (hpre : ∀ t ≤ i, x.1.mu t = y.1.mu t)
    (hext : (⟨xpath x.1 hi hx hL, xfill x.2.1 L, isStdFilling_xfill x.1.mu i μ₀ x.2.2 hi⟩ :
      PathIdx n (n + (N - i)) (xvec i n vec) (xB i B μ₀ L)) =
      ⟨xpath y.1 hi hy hL, xfill y.2.1 L, isStdFilling_xfill y.1.mu i μ₀ y.2.2 hi⟩) : x = y := by
  have hmu : xmu i x.1.mu μ₀ L = xmu i y.1.mu μ₀ L :=
    congrArg (fun z : PathIdx n (n + (N - i)) (xvec i n vec) (xB i B μ₀ L) => z.1.mu) hext
  have hfill : xfill x.2.1 L = xfill y.2.1 L :=
    congrArg (fun z : PathIdx n (n + (N - i)) (xvec i n vec) (xB i B μ₀ L) => z.2.1) hext
  have hP : x.1.mu = y.1.mu := by
    funext t a
    by_cases ht : t ≤ i
    · rw [hpre t ht]
    · have h := congrFun (congrFun hmu (n + (t - i))) a
      rw [xmu_ge, xmu_ge, Nat.add_sub_cancel' (by omega : i ≤ t)] at h
      linarith
  have hI : x.2.1 = y.2.1 := by
    apply colSet_injective
    funext c
    have h := congrFun (colSet_injective hfill) (c - L)
    simpa using h
  obtain ⟨P, I, hI'⟩ := x
  obtain ⟨Q, J, hJ'⟩ := y
  have hPQ : P = Q := PieriPath.ext' hP
  subst hPQ
  simp only at hI
  subst hI
  rfl

variable (R N vec B) in
/-- **(E3) Top components are independent** (domains): for a dominant `μ₀`, the weight-`μ₀` components of the
generic translates through the first `i` letters of the `Ψ(x)` with `μ_i = μ₀` are `R`-linearly independent.
Route: `top_identity` writes each as `±det(g)^e·Ψ(P|_{≤i}, can)·κ·xsub(Ψ'(x'))` up to a common constant; the first
factors are prefix path-basis members (letters `< i`), the last ones images of distinct members of the extended path
basis under the injective `xsub` (letters `≥ i`); `tensor_indep` separates the prefix fibres. -/
theorem top_linearIndependent [IsDomain R] {m : ℕ} {i : ℕ} (hi : i ≤ N) (μ₀ : Fin (m + 1) → ℤ) :
    LinearIndependent R (fun x : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} =>
      gcomp vec (Set.Iio i) μ₀ (pathFam R x.1)) := by
  classical
  let _ : Fintype (PathIdx (m + 1) N vec B) := Fintype.ofFinite _
  let _ : Fintype (PathIdx (m + 1) i vec B) := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff]
  intro g hg x₀
  have hanti : Antitone μ₀ := x₀.2 ▸ x₀.1.1.antitone i
  set L : ℤ := ∑ a, |μ₀ a| with hLdef
  have hL : ∀ a, μ₀ a ≤ L := fun a =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun b => |μ₀ b|) (fun b _ => abs_nonneg _) (mem_univ a))
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun a _ => abs_nonneg _
  -- a common window
  let bd : PathIdx (m + 1) N vec B → ℤ := fun x => (∑ t ∈ range (N + 1), ∑ a, |x.1.mu t a|) +
    (∑ t ∈ range (m + 1 + (N - i) + 1), ∑ a, |xmu i x.1.mu μ₀ L t a|) + L
  set T : ℤ := (((univ : Finset (PathIdx (m + 1) N vec B)).sup fun x => (bd x).toNat : ℕ) : ℤ) with hTdef
  have hbd : ∀ x, bd x ≤ T := fun x =>
    (Int.self_le_toNat _).trans (Nat.cast_le.2 (Finset.le_sup (f := fun x => (bd x).toNat) (mem_univ x)))
  have hnn : ∀ (μ : ℕ → Fin (m + 1) → ℤ) (K : ℕ), 0 ≤ ∑ t ∈ range K, ∑ a, |μ t a| :=
    fun μ K => Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun a _ => abs_nonneg _
  have hT1 : ∀ x : PathIdx (m + 1) N vec B, colRange x.1.mu N ⊆ Icc (-T) T := fun x c hc => by
    have h1 := hbd x
    have h2 := hnn (xmu i x.1.mu μ₀ L) (m + 1 + (N - i) + 1)
    simp only [colRange, mem_Icc, bd] at hc h1 ⊢
    constructor <;> linarith [hc.1, hc.2]
  have hT2 : ∀ x : PathIdx (m + 1) N vec B,
      colRange (xmu i x.1.mu μ₀ L) (m + 1 + (N - i)) ⊆ Icc (-T - L) (T - L) := fun x c hc => by
    have h1 := hbd x
    have h2 := hnn x.1.mu (N + 1)
    simp only [colRange, mem_Icc, bd] at hc h1 ⊢
    constructor <;> linarith [hc.1, hc.2]
  -- the identities
  choose s hs hid using fun x : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} =>
    top_identity (R := R) x.1.1 x.1.2.2 hi x.2 hanti hL (hT1 x.1) (hT2 x.1)
  set kW : SymbolData.GenCoeff ℕ R (m + 1) := ∏ c ∈ Icc (-T) T, kap c
  set kX : SymbolData.GenCoeff ℕ R (m + 1) :=
    ∏ c ∈ Icc (-T) T, if L + 1 ≤ c then W (Aw (R := R) false) univ univ else 1
  set d : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} → ℕ :=
    fun x => ∑ c ∈ Icc (-T) T, ncon (dstep x.1.1.mu c) i
  have hμt : ∀ x : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀}, (truncP x.1.1 i hi).mu i = μ₀ := fun x => by
    simp [truncP, x.2]
  let pre : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} → PathIdx (m + 1) i vec B := fun x =>
    ⟨truncP x.1.1 i hi, canFill μ₀, by rw [hμt x]; exact isStdFilling_canFill μ₀⟩
  let ext : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} →
      PathIdx (m + 1) (m + 1 + (N - i)) (xvec i (m + 1) vec) (xB i B μ₀ L) := fun x =>
    ⟨xpath x.1.1 hi x.2 hL, xfill x.1.2.1 L, isStdFilling_xfill x.1.1.mu i μ₀ x.1.2.2 hi⟩
  have hpreF : ∀ x, pathPoly R x.1.1.mu i (canFill μ₀) = pathFam R (pre x) := fun x =>
    pathPoly_congr (fun t ht => by simp [pre, truncP, min_eq_left ht]) _
  have hextF : ∀ x, pathPoly R (xmu i x.1.1.mu μ₀ L) (m + 1 + (N - i)) (xfill x.1.2.1 L) = pathFam R (ext x) :=
    fun x => rfl
  -- the signs are `±1`
  let e : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} → R := fun x => if s x = 1 then 1 else -1
  have he : ∀ x, s x = algebraMap R _ (e x) := fun x => by
    by_cases h1 : s x = 1
    · simp [e, h1]
    · have := (mul_self_eq_one_iff.1 (hs x)).resolve_left h1
      simp only [e, h1, ite_false, map_neg, map_one]
      exact this
  have hee : ∀ x, e x * e x = 1 := fun x => by simp only [e]; split_ifs <;> ring
  -- the relation, through the prefix fibres
  let V : {x : PathIdx (m + 1) N vec B // x.1.mu i = μ₀} → SymbolData.GenCoeff ℕ R (m + 1) := fun x =>
    algebraMap R _ (g x * e x) * MvPolynomial.C (genMat R (m + 1)).det ^ d x * kX *
      xsub R (m + 1) i (pathFam R (ext x))
  have h1 : ∑ x, MvPolynomial.map MvPolynomial.C (pathFam R (pre x)) * V x = 0 := by
    have h := congrArg (kW * ·) hg
    simp only [mul_zero, Finset.mul_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul_comm]
    have hx : kW * gcomp vec (Set.Iio i) μ₀ (pathFam R x.1) = _ := hid x
    rw [hx, he x, hpreF, hextF]
    simp only [V, Algebra.smul_def, map_mul]
    ring
  have h2 : ∑ k, MvPolynomial.map MvPolynomial.C (pathFam R k) *
      (∑ x ∈ univ.filter fun x => pre x = k, V x) = 0 := by
    rw [← h1, ← Finset.sum_fiberwise univ pre]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2]
  have hu := pathFam_linearIndependent R m i vec B
  have hC : ∀ a : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R, (MvPolynomial.C a : SymbolData.GenCoeff ℕ R (m + 1)) ∈
      supported (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) {v : ℕ × Fin (m + 1) | i ≤ v.1} :=
    fun a => Subalgebra.algebraMap_mem _ a
  have hV : ∀ x, V x ∈ supported (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) {v : ℕ × Fin (m + 1) | i ≤ v.1} :=
    fun x => by
      have h0 : algebraMap R (SymbolData.GenCoeff ℕ R (m + 1)) (g x * e x) =
          MvPolynomial.C (MvPolynomial.C (g x * e x)) := by
        rw [MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      have hk : kX ∈ supported (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) {v : ℕ × Fin (m + 1) | i ≤ v.1} := by
        refine Subalgebra.prod_mem _ fun c _ => ?_
        split_ifs
        · rw [W_Aw_false_eq]; exact hC _
        · exact Subalgebra.one_mem _
      simp only [V, h0]
      exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hC _)
        (Subalgebra.pow_mem _ (hC _) _)) hk) (xsub_supported i _)
  have hW := tensor_indep (pathFam R) hu (fun k => pathPoly_supported _ _ _)
    (fun k => ∑ x ∈ univ.filter fun x => pre x = k, V x)
    (fun k => support_of_supported (Subalgebra.sum_mem _ fun x _ => hV x)) h2 (pre x₀)
  -- inside the fibre of `x₀`
  have hfib : ∀ x, pre x = pre x₀ → ∀ t ≤ i, x.1.1.mu t = x₀.1.1.mu t := fun x hx t ht => by
    have := congrFun (congrArg (fun z : PathIdx (m + 1) i vec B => z.1.mu) hx) t
    simpa [pre, truncP, min_eq_left ht] using this
  have hd : ∀ x, pre x = pre x₀ → d x = d x₀ := fun x hx => by
    refine Finset.sum_congr rfl fun c _ => ncon_congr fun u hu => ?_
    unfold dstep
    rw [hfib x hx u (by omega), hfib x hx (u + 1) (by omega)]
  have hdet : (MvPolynomial.C (genMat R (m + 1)).det : SymbolData.GenCoeff ℕ R (m + 1)) ≠ 0 :=
    fun h => Matrix.det_mvPolynomialX_ne_zero (Fin (m + 1)) R ((MvPolynomial.C_eq_zero).1 h)
  have hkX : kX ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => by
    split_ifs
    · exact kap_ne_zero
    · exact one_ne_zero
  have h3 : xsub R (m + 1) i (∑ x ∈ univ.filter fun x => pre x = pre x₀, (g x * e x) • pathFam R (ext x)) = 0 := by
    have h4 : (∑ x ∈ univ.filter fun x => pre x = pre x₀, V x) =
        MvPolynomial.C (genMat R (m + 1)).det ^ d x₀ * kX *
          xsub R (m + 1) i (∑ x ∈ univ.filter fun x => pre x = pre x₀, (g x * e x) • pathFam R (ext x)) := by
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [V]
      rw [xsub_smul, Algebra.smul_def, hd x (mem_filter.1 hx).2]
      ring
    rw [h4] at hW
    exact (mul_eq_zero.1 hW).resolve_left (mul_ne_zero (pow_ne_zero _ hdet) hkX)
  have h5 := (map_eq_zero_iff _ (xsub_injective i)).1 h3
  -- the extended family on the fibre is independent
  have hinj : Function.Injective (fun y : {x // pre x = pre x₀} => ext y.1) := by
    intro y₁ y₂ h
    have hpre : ∀ t ≤ i, y₁.1.1.1.mu t = y₂.1.1.1.mu t := fun t ht =>
      (hfib y₁.1 y₁.2 t ht).trans (hfib y₂.1 y₂.2 t ht).symm
    exact Subtype.ext (Subtype.ext (ext_injective hi hL y₁.1.2 y₂.1.2 hpre h))
  have hind : LinearIndependent R (fun y : {x // pre x = pre x₀} => pathFam R (ext y.1)) :=
    (pathFam_linearIndependent R m (m + 1 + (N - i)) (xvec i (m + 1) vec) (xB i B μ₀ L)).comp _ hinj
  have h6 : ∑ y : {x // pre x = pre x₀}, (g y.1 * e y.1) • pathFam R (ext y.1) = 0 := by
    rw [← h5]
    exact (Finset.sum_subtype _ (fun x => by simp) (fun x => (g x * e x) • pathFam R (ext x))).symm
  have h7 := (Fintype.linearIndependent_iff.1 hind) (fun y => g y.1 * e y.1) h6 ⟨x₀, rfl⟩
  calc g x₀ = g x₀ * e x₀ * e x₀ := by rw [mul_assoc, hee, mul_one]
    _ = 0 := by rw [h7, zero_mul]

end E3

end

end CapacitySpan
