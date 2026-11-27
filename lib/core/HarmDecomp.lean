import LetterFock

/-!
# The harmonic decomposition of letter-pair polynomials, with denominators

The algebraic half of L5's harmonic splitting (A-N7): for two letters `a ≠ b` with `k` coordinates (polynomials in
letters, `LetterFock.LPol`), the pairing `h = Σ_c X_{a,c}X_{b,c}` (`hP`) and the pair Laplacian
`Δ = Σ_c ∂_{a,c}∂_{b,c}` (`lapP`) split every polynomial of degrees `(P, Q)` in `(a, b)` as `Σ_{j ≤ min(P, Q)} h^j·f_j`
with `Δf_j = 0`, by explicit operators `f_j` (`fj`) whose coefficients are inverses of binomial coefficients.

**Degrees.** Polynomials are multihomogeneous (`LHom d`, `d` the degree in each letter). Along a chain the degrees in
`a, b` are `d₀ + i·(e_a + e_b)` (`pe`), with `min(d₀_a, d₀_b) = 0`; then `u = k + d₀_a + d₀_b` is constant along the
chain and `Δ(hF) = hΔF + (u + 2i)F` on degree `d₀ + i·pe` (`lapP_hP_mul`, from Euler's identity).

**Main results.**
* *No negative eigenvalues* (`eq_zero_of_hP_lapP`): `hΔF = −cF` with `c > 0` forces `F = 0` (apply `Δ` and induct);
  so `Δ(hF) = 0` forces `F = 0` (`eq_zero_of_lapP_hP`).
* *The harmonic projection* `π₀ = Σ_{r ≤ i} c_r h^rΔ^r`, `c_r = (−1)^r/(r!²·C(u + 2i − 2, r))` (`pi0`): `Δπ₀F = 0`
  (`lapP_pi0`, a telescoping sum), `π₀F = F + h·ρF` (`pi0_eq`), `π₀(hY) = 0` (`pi0_hP_mul`), `π₀F = F` for harmonic
  `F` (`pi0_of_lapP`).
* *The decomposition* (`sum_fj`): `F = Σ_{j ≤ i} h^j·f_j(F)`, `f_j = (j!²·C(u + 2i − j − 1, j))⁻¹·π₀Δ^j` (`fj`), by
  induction on `i` through `f_{j+1}(F) = f_j(−ρF)` (`fj_succ`), from `Δ^{m+1}(hY) = hΔ^{m+1}Y + (m + 1)(w − m)Δ^mY`
  (`lapP_pow_hP_mul`).
* *Denominators* (`fj_mem_intP`): over a subring `A` in which the integers prime to `p` are invertible,
  `p^{(k + 1)L}·f_j` keeps the `A`-integral polynomials (`intP`) when `⌊log_p(u + 2i)⌋ ≤ L`: the divided Laplacian
  `Δ^m/m!²` loses `p^{(k − 1)⌊log_p m⌋}` (`lapP_pow_mem_intP`, binomial expansion over the coordinates,
  `v_p C(m, i) ≤ ⌊log_p m⌋`), and `f_j = Σ_r ±C(r + j, j)²/(C(M, j)C(N, r))·h^r·Δ^{r+j}/(r + j)!²` loses two more
  `⌊log_p⌋`s.
* *Several positions* (`Pairs`, disjoint letter pairs `(a_s, b_s)`): the projector of a list of positions (`piL`) has
  `F = Σ_j (∏_s h_s^{j_s})·π_j(F)` (`Pairs.sum_piL`), harmonic values (`Pairs.lapP_piL`), the chain degrees
  (`piL_mem`), denominators `p^{Σ_s (k + 1)L_s}` (`piL_mem_intP`), `β(π₀F) = β(F)` for algebra maps killing the
  pairings (`map_piL_zero`), `π₀F = F` for harmonic `F` (`piL_zero_of_lapP`), and commutes with letter changes
  `A` with `A_aᵀA_b = A_aA_bᵀ = γ·1` up to `∏_s γ_s^{j_s}` (`piL_linS`).
-/

namespace HarmDecomp

open MvPolynomial LetterFock Finset

open scoped Matrix

noncomputable section

/-! ## The pairing, the pair Laplacian and degrees -/

section Pair

variable {α : Type*} [DecidableEq α] {k : ℕ} {K : Type*} [Field K]

/-- **The pairing polynomial** `h_{ab} = Σ_c X_{a,c}X_{b,c}` of two letters. -/
def hP (a b : α) : LPol α k K := ∑ c, X (a, c) * X (b, c)

/-- **The pair Laplacian** `Δ_{ab} = Σ_c ∂_{a,c}∂_{b,c}`. -/
def lapP (a b : α) : Module.End K (LPol α k K) :=
  ∑ c, (pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap

/-- **The degree of the pairing**: `e_a + e_b`. -/
def pe (a b : α) : α → ℕ := Pi.single a 1 + Pi.single b 1

omit [DecidableEq α] in
/-- **The pair Laplacian**, unfolded. -/
theorem lapP_apply (a b : α) (F : LPol α k K) : lapP a b F = ∑ c, pderiv (a, c) (pderiv (b, c) F) := by
  simp [lapP, LinearMap.sum_apply]

/-- **The derivative of the pairing** in the letter `a`. -/
theorem pderiv_hP_left {a b : α} (hab : a ≠ b) (c : Fin k) : pderiv (a, c) (hP a b : LPol α k K) = X (b, c) := by
  simp only [hP, map_sum, pderiv_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and,
    show b ≠ a from Ne.symm hab, false_and, ite_false, mul_zero, add_zero]
  simp [eq_comm]

/-- **The derivative of the pairing** in the letter `b`. -/
theorem pderiv_hP_right {a b : α} (hab : a ≠ b) (c : Fin k) : pderiv (b, c) (hP a b : LPol α k K) = X (a, c) := by
  simp only [hP, map_sum, pderiv_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and, hab, false_and,
    ite_false, zero_mul, zero_add]
  simp [eq_comm]

/-- **The derivative of the pairing** in another letter vanishes. -/
theorem pderiv_hP_other {a b l : α} (ha : l ≠ a) (hb : l ≠ b) (c : Fin k) :
    pderiv (l, c) (hP a b : LPol α k K) = 0 := by
  simp [hP, map_sum, pderiv_X, Ne.symm ha, Ne.symm hb]

/-- **A derivative lowers the degree** of its letter by one. -/
theorem pderiv_mem_LHom {d : α → ℕ} {l : α} (c : Fin k) {F : LPol α k K}
    (hF : F ∈ LHom K (d + Pi.single l 1)) : pderiv (l, c) F ∈ LHom K d := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF ⊢
  intro m hm
  rw [coeff_pderiv] at hm
  have h := hF (left_ne_zero_of_mul hm)
  rw [map_add, Finsupp.weight_single, one_smul] at h
  exact add_right_cancel h

/-- **A derivative in a letter of degree `0`** vanishes. -/
theorem pderiv_eq_zero_of_LHom [Fintype α] {d : α → ℕ} {l : α} (hl : d l = 0) (c : Fin k) {F : LPol α k K}
    (hF : F ∈ LHom K d) : pderiv (l, c) F = 0 := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF
  ext m
  rw [coeff_pderiv]
  show _ = (0 : K)
  by_contra hm
  have h := congrFun (hF (left_ne_zero_of_mul hm)) l
  rw [weight_rowW_apply, hl, Finset.sum_eq_zero_iff] at h
  have := h c (Finset.mem_univ _)
  simp at this

/-- **The pairing has degree `e_a + e_b`.** -/
theorem hP_mem (a b : α) : (hP a b : LPol α k K) ∈ LHom K (pe a b) := by
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [LHom, mem_weightedHomogeneousSubmodule]
  exact (isWeightedHomogeneous_X K (rowW α k) (a, c)).mul (isWeightedHomogeneous_X K (rowW α k) (b, c))

/-- **Multiplying by `h^r`** raises the degree by `r·(e_a + e_b)`. -/
theorem hP_pow_mul_mem (a b : α) (r : ℕ) {d : α → ℕ} {F : LPol α k K} (hF : F ∈ LHom K d) :
    hP a b ^ r * F ∈ LHom K (d + r • pe a b) := by
  rw [LHom, mem_weightedHomogeneousSubmodule] at hF ⊢
  have := ((hP_mem (k := k) (K := K) a b).pow r).mul hF
  rwa [add_comm] at this

/-- **Multiplying by `h`** raises the degree by `e_a + e_b`. -/
theorem hP_mul_mem (a b : α) {d : α → ℕ} {F : LPol α k K} (hF : F ∈ LHom K d) :
    hP a b * F ∈ LHom K (d + pe a b) := by
  simpa using hP_pow_mul_mem a b 1 hF

/-- **`Δ` lowers the degree** by `e_a + e_b`. -/
theorem lapP_mem {a b : α} {d : α → ℕ} {F : LPol α k K} (hF : F ∈ LHom K (d + pe a b)) :
    lapP a b F ∈ LHom K d := by
  rw [lapP_apply]
  refine Submodule.sum_mem _ fun c _ => pderiv_mem_LHom c (pderiv_mem_LHom c ?_)
  rwa [pe, ← add_assoc] at hF

/-- **`Δ` vanishes** when one of the two letters has degree `0`. -/
theorem lapP_eq_zero [Fintype α] {a b : α} {d : α → ℕ} (hd : d a = 0 ∨ d b = 0) {F : LPol α k K} (hF : F ∈ LHom K d) :
    lapP a b F = 0 := by
  rw [lapP_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases hd with h | h
  · by_cases hb : d b = 0
    · rw [pderiv_eq_zero_of_LHom hb c hF, map_zero]
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + Pi.single b 1 :=
        ⟨d - Pi.single b 1, funext fun l => by
          by_cases hl : l = b
          · subst hl; simp; omega
          · simp [hl]⟩
      refine pderiv_eq_zero_of_LHom ?_ c (pderiv_mem_LHom c hF)
      by_cases hab : a = b
      · subst hab; simp at h
      · simpa [Pi.single_apply, hab] using h
  · rw [pderiv_eq_zero_of_LHom h c hF, map_zero]

/-- **Euler's identity** for a letter: `Σ_c X_{l,c}∂_{l,c}F = d_l·F` on degree `d`. -/
theorem sum_X_mul_pderiv [Fintype α] {d : α → ℕ} {F : LPol α k K} (hF : F ∈ LHom K d) (l : α) :
    ∑ c, X (l, c) * pderiv (l, c) F = (d l : K) • F := by
  have hw : IsWeightedHomogeneous (fun v : α × Fin k => if l = v.1 then 1 else 0) F (d l) := by
    intro m hm
    rw [LHom, mem_weightedHomogeneousSubmodule] at hF
    have h := congrFun (hF hm) l
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h
    rw [Finsupp.weight_apply, Finsupp.sum, ← h]
    simp [rowW, Pi.single_apply]
  have h := hw.sum_weight_X_mul_pderiv
  rw [Fintype.sum_prod_type, Finset.sum_eq_single l (fun l' _ hl' => by simp [Ne.symm hl']) (by simp)] at h
  simpa [← Nat.cast_smul_eq_nsmul K] using h

/-- **The commutator** `[Δ, h]` without degrees: `Δ(hF) = hΔF + k·F + E_aF + E_bF`. -/
theorem lapP_hP_mul_aux {a b : α} (hab : a ≠ b) (F : LPol α k K) :
    lapP a b (hP a b * F) = hP a b * lapP a b F + (k : K) • F + ∑ c, X (a, c) * pderiv (a, c) F +
      ∑ c, X (b, c) * pderiv (b, c) F := by
  have h1 : ∀ c, pderiv (b, c) (hP a b * F) = X (a, c) * F + hP a b * pderiv (b, c) F := fun c => by
    rw [pderiv_mul, pderiv_hP_right hab]
  have h2 : ∀ c, pderiv (a, c) (pderiv (b, c) (hP a b * F)) =
      F + X (a, c) * pderiv (a, c) F + X (b, c) * pderiv (b, c) F +
        hP a b * pderiv (a, c) (pderiv (b, c) F) := fun c => by
    rw [h1, map_add, pderiv_mul, pderiv_mul, pderiv_X_self, pderiv_hP_left hab]
    ring
  rw [lapP_apply, lapP_apply, Finset.sum_congr rfl fun c _ => h2 c, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, ← Nat.cast_smul_eq_nsmul K]
  ring

/-- **The commutator** `Δ(hF) = hΔF + (k + d_a + d_b)·F` on degree `d`. -/
theorem lapP_hP_mul [Fintype α] {a b : α} (hab : a ≠ b) {d : α → ℕ} {F : LPol α k K} (hF : F ∈ LHom K d) :
    lapP a b (hP a b * F) = hP a b * lapP a b F + ((k + d a + d b : ℕ) : K) • F := by
  rw [lapP_hP_mul_aux hab, sum_X_mul_pderiv hF, sum_X_mul_pderiv hF]
  push_cast
  rw [add_smul, add_smul]
  ring

end Pair

/-! ## Chains: degrees `d₀ + i·(e_a + e_b)` -/

section Chain

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {K : Type*} [Field K] {a b : α}

omit [Fintype α] in
/-- **The pairing degree at `a`** is `1`. -/
theorem pe_left (hab : a ≠ b) : pe a b a = 1 := by simp [pe, hab]

omit [Fintype α] in
/-- **The pairing degree at `b`** is `1`. -/
theorem pe_right (hab : a ≠ b) : pe a b b = 1 := by simp [pe, Ne.symm hab]

omit [Fintype α] in
/-- **`Δ^m` on a chain** lowers the step by `m`. -/
theorem lapP_pow_mem {d₀ : α → ℕ} {i m : ℕ} (hm : m ≤ i) {F : LPol α k K} (hF : F ∈ LHom K (d₀ + i • pe a b)) :
    (lapP a b ^ m) F ∈ LHom K (d₀ + (i - m) • pe a b) := by
  induction m with
  | zero => simpa using hF
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := ih (by omega)
    rw [show i - m = (i - (m + 1)) + 1 by omega, add_smul, one_smul, ← add_assoc] at h
    exact lapP_mem h

/-- **`Δ^m` vanishes on a chain** beyond its length. -/
theorem lapP_pow_eq_zero {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i m : ℕ} (hm : i < m) {F : LPol α k K}
    (hF : F ∈ LHom K (d₀ + i • pe a b)) : (lapP a b ^ m) F = 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + (i + 1) := ⟨m - (i + 1), by omega⟩
  have h := lapP_pow_mem (le_refl i) hF
  rw [Nat.sub_self, zero_smul, add_zero] at h
  rw [pow_add, Module.End.mul_apply, pow_succ', Module.End.mul_apply, lapP_eq_zero h0 h, map_zero]

/-- **The commutator on a chain**: `Δ(hF) = hΔF + (u + 2i)·F`, `u = k + d₀_a + d₀_b`. -/
theorem lapP_hP_mul_chain (hab : a ≠ b) {d₀ : α → ℕ} {i : ℕ} {F : LPol α k K}
    (hF : F ∈ LHom K (d₀ + i • pe a b)) :
    lapP a b (hP a b * F) = hP a b * lapP a b F + ((k + d₀ a + d₀ b + 2 * i : ℕ) : K) • F := by
  rw [lapP_hP_mul hab hF]
  congr 3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pe_left hab, pe_right hab]
  ring

/-- **The commutator with `h^{r+1}`** on a chain:
`Δ(h^{r+1}F) = h^{r+1}ΔF + (r + 1)(u + 2i + r)·h^rF`. -/
theorem lapP_hP_pow_mul (hab : a ≠ b) {d₀ : α → ℕ} {i : ℕ} {F : LPol α k K}
    (hF : F ∈ LHom K (d₀ + i • pe a b)) (r : ℕ) :
    lapP a b (hP a b ^ (r + 1) * F) = hP a b ^ (r + 1) * lapP a b F +
      (((r + 1) * (k + d₀ a + d₀ b + 2 * i + r) : ℕ) : K) • (hP a b ^ r * F) := by
  induction r with
  | zero => simpa using lapP_hP_mul_chain hab hF
  | succ r ih =>
    have hG : hP a b ^ (r + 1) * F ∈ LHom K (d₀ + (i + (r + 1)) • pe a b) := by
      rw [add_smul, ← add_assoc]
      exact hP_pow_mul_mem a b (r + 1) hF
    rw [pow_succ', mul_assoc, lapP_hP_mul_chain hab hG, ih, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ',
      ← mul_assoc (hP a b) (hP a b ^ r) F, ← pow_succ' (hP a b) r, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

variable [CharZero K]

/-- **No negative eigenvalues** of `hΔ` on a chain: `hΔF = −c·F` with `c > 0` forces `F = 0`. -/
theorem eq_zero_of_hP_lapP (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) :
    ∀ (i c : ℕ) (F : LPol α k K), 0 < c → F ∈ LHom K (d₀ + i • pe a b) →
      hP a b * lapP a b F = -((c : ℕ) : K) • F → F = 0 := by
  intro i
  induction i with
  | zero =>
    intro c F hc hF h
    rw [zero_smul, add_zero] at hF
    rw [lapP_eq_zero h0 hF, mul_zero, eq_comm, neg_smul, neg_eq_zero, smul_eq_zero] at h
    exact h.resolve_left (Nat.cast_ne_zero.2 hc.ne')
  | succ i ih =>
    intro c F hc hF h
    have hG : lapP a b F ∈ LHom K (d₀ + i • pe a b) := lapP_mem (by rwa [add_smul, one_smul, ← add_assoc] at hF)
    have h2 := congrArg (lapP a b) h
    rw [lapP_hP_mul_chain hab hG, map_smul] at h2
    have h3 := ih (c + (k + d₀ a + d₀ b + 2 * i)) (lapP a b F) (by omega) hG
      (by rw [eq_sub_of_add_eq h2]; push_cast; module)
    rw [h3, mul_zero, eq_comm, neg_smul, neg_eq_zero, smul_eq_zero] at h
    exact h.resolve_left (Nat.cast_ne_zero.2 hc.ne')

/-- **A multiple of `h` is not harmonic**: `Δ(hF) = 0` forces `F = 0` (`k ≥ 1`). -/
theorem eq_zero_of_lapP_hP (hk : 1 ≤ k) (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i : ℕ}
    {F : LPol α k K} (hF : F ∈ LHom K (d₀ + i • pe a b)) (h : lapP a b (hP a b * F) = 0) : F = 0 := by
  rw [lapP_hP_mul_chain hab hF, add_eq_zero_iff_eq_neg, ← neg_smul] at h
  exact eq_zero_of_hP_lapP hab h0 i _ F (by omega) hF h

/-- **The commutator with `Δ^{m+1}`** on a chain: `Δ^{m+1}(hY) = hΔ^{m+1}Y + (m + 1)(u + 2i − m)·Δ^mY`. -/
theorem lapP_pow_hP_mul (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i : ℕ} {Y : LPol α k K}
    (hY : Y ∈ LHom K (d₀ + i • pe a b)) (m : ℕ) :
    (lapP a b ^ (m + 1)) (hP a b * Y) = hP a b * (lapP a b ^ (m + 1)) Y +
      (((m + 1 : ℕ) : K) * (((k + d₀ a + d₀ b + 2 * i : ℕ) : K) - m)) • (lapP a b ^ m) Y := by
  induction m with
  | zero => simpa using lapP_hP_mul_chain hab hY
  | succ m ih =>
    rw [pow_succ' _ (m + 1), Module.End.mul_apply, Module.End.mul_apply, ih, map_add, map_smul,
      ← Module.End.mul_apply (lapP a b) (lapP a b ^ m), ← pow_succ']
    by_cases hm : m + 1 ≤ i
    · rw [lapP_hP_mul_chain hab (lapP_pow_mem hm hY), add_assoc, ← add_smul]
      congr 2
      push_cast [Nat.cast_sub hm]
      ring
    · rw [lapP_pow_eq_zero h0 (show i < m + 1 by omega) hY]
      simp

end Chain

/-! ## The harmonic projection and the decomposition -/

section Proj

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {K : Type*} [Field K] [CharZero K] {a b : α}

variable (K) in
/-- **The coefficient of the harmonic projection** `c_r = (−1)^r/(r!²·C(N, r))`. -/
def cπ (N r : ℕ) : K := (-1) ^ r / ((r.factorial : K) ^ 2 * (N.choose r : K))

variable (K) in
/-- **The coefficient of the harmonic pieces** `1/(j!²·C(M, j))`. -/
def cf (M j : ℕ) : K := 1 / ((j.factorial : K) ^ 2 * (M.choose j : K))

variable (k K) in
/-- **The harmonic projection** on the step `i` of a chain with constant `u`:
`π₀ = Σ_{r ≤ i} c_r·h^rΔ^r`, `c_r = cπ (u + 2i − 2) r`. -/
def pi0 (a b : α) (u i : ℕ) : Module.End K (LPol α k K) :=
  ∑ r ∈ range (i + 1), cπ K (u + 2 * i - 2) r • (LinearMap.mulLeft K (hP a b ^ r) * lapP a b ^ r)

variable (k K) in
/-- **The correction** `ρ = Σ_{r < i} c_{r+1}·h^rΔ^{r+1}`, so that `π₀ = 1 + h·ρ`. -/
def rho (a b : α) (u i : ℕ) : Module.End K (LPol α k K) :=
  ∑ r ∈ range i, cπ K (u + 2 * i - 2) (r + 1) • (LinearMap.mulLeft K (hP a b ^ r) * lapP a b ^ (r + 1))

variable (k K) in
/-- **The harmonic piece** `f_j = (j!²·C(u + 2i − j − 1, j))⁻¹·π₀Δ^j` on the step `i`. -/
def fj (a b : α) (u i j : ℕ) : Module.End K (LPol α k K) :=
  cf K (u + 2 * i - j - 1) j • (pi0 k K a b u (i - j) * lapP a b ^ j)

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **The harmonic projection**, unfolded. -/
theorem pi0_apply (u i : ℕ) (F : LPol α k K) :
    pi0 k K a b u i F = ∑ r ∈ range (i + 1), cπ K (u + 2 * i - 2) r • (hP a b ^ r * (lapP a b ^ r) F) := by
  simp [pi0, LinearMap.sum_apply]

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **The correction**, unfolded. -/
theorem rho_apply (u i : ℕ) (F : LPol α k K) :
    rho k K a b u i F = ∑ r ∈ range i, cπ K (u + 2 * i - 2) (r + 1) • (hP a b ^ r * (lapP a b ^ (r + 1)) F) := by
  simp [rho, LinearMap.sum_apply]

omit [CharZero K] in
/-- **`c₀ = 1`.** -/
theorem cπ_zero (N : ℕ) : cπ K N 0 = 1 := by simp [cπ]

omit [CharZero K] in
/-- **`1/(0!²·C(M, 0)) = 1`.** -/
theorem cf_zero (M : ℕ) : cf K M 0 = 1 := by simp [cf]

/-- **The telescoping identity** `c_r + c_{r+1}·(r + 1)(N − r) = 0` for `r < N`. -/
theorem cπ_succ {N r : ℕ} (h : r < N) :
    cπ K N r + cπ K N (r + 1) * (((r + 1) * (N - r) : ℕ) : K) = 0 := by
  have hC : ((N.choose (r + 1) : ℕ) : K) * ((r : K) + 1) = (N.choose r : K) * ((N - r : ℕ) : K) := by
    exact_mod_cast Nat.choose_succ_right_eq N r
  have hD1 : (r.factorial : K) ^ 2 * (N.choose r : K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)))
      (Nat.cast_ne_zero.2 (Nat.choose_pos h.le).ne')
  have hD2 : ((r + 1).factorial : K) ^ 2 * (N.choose (r + 1) : K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)))
      (Nat.cast_ne_zero.2 (Nat.choose_pos h).ne')
  rw [cπ, cπ, div_mul_eq_mul_div, div_add_div _ _ hD1 hD2, div_eq_zero_iff]
  left
  rw [Nat.factorial_succ]
  push_cast
  linear_combination (-1 : K) ^ r * ((r : K) + 1) * (r.factorial : K) ^ 2 * hC

/-- **The recursion of the piece coefficients** `cf(M, j + 1)·(j + 1)·M = cf(M − 1, j)` for `j < M`. -/
theorem cf_succ {M j : ℕ} (h : j < M) :
    cf K M (j + 1) * (((j + 1 : ℕ) : K) * (M : K)) = cf K (M - 1) j := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hC : ((M : K) + 1) * (M.choose j : K) = ((M + 1).choose (j + 1) : K) * ((j : K) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq M j
  have hD1 : (j.factorial : K) ^ 2 * (M.choose j : K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)))
      (Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne')
  have hD2 : ((j + 1).factorial : K) ^ 2 * ((M + 1).choose (j + 1) : K) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)))
      (Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne')
  rw [cf, cf, Nat.add_sub_cancel, div_mul_eq_mul_div, div_eq_div_iff hD2 hD1, Nat.factorial_succ]
  push_cast
  linear_combination ((j : K) + 1) * (j.factorial : K) ^ 2 * hC

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **`π₀ = 1 + h·ρ`.** -/
theorem pi0_eq (u i : ℕ) (F : LPol α k K) : pi0 k K a b u i F = F + hP a b * rho k K a b u i F := by
  rw [pi0_apply, rho_apply, Finset.sum_range_succ', cπ_zero, pow_zero, one_mul, pow_zero,
    Module.End.one_apply, one_smul, add_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_smul_comm, ← mul_assoc, ← pow_succ']

omit [Fintype α] [CharZero K] in
/-- **The correction lowers the step by one.** -/
theorem rho_mem {d₀ : α → ℕ} {u i : ℕ} {F : LPol α k K} (hF : F ∈ LHom K (d₀ + (i + 1) • pe a b)) :
    rho k K a b u (i + 1) F ∈ LHom K (d₀ + i • pe a b) := by
  rw [rho_apply]
  refine Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_
  have hr := Finset.mem_range.1 hr
  have h := hP_pow_mul_mem a b r (lapP_pow_mem (show r + 1 ≤ i + 1 by omega) hF)
  rwa [add_assoc, ← add_smul, show i + 1 - (r + 1) + r = i by omega] at h

omit [Fintype α] [CharZero K] in
/-- **The harmonic projection keeps the degree.** -/
theorem pi0_mem {d₀ : α → ℕ} {u i : ℕ} {F : LPol α k K} (hF : F ∈ LHom K (d₀ + i • pe a b)) :
    pi0 k K a b u i F ∈ LHom K (d₀ + i • pe a b) := by
  rw [pi0_apply]
  refine Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _ ?_
  have hr := Finset.mem_range.1 hr
  have h := hP_pow_mul_mem a b r (lapP_pow_mem (show r ≤ i by omega) hF)
  rwa [add_assoc, ← add_smul, show i - r + r = i by omega] at h

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **The harmonic projection fixes harmonic polynomials.** -/
theorem pi0_of_lapP {u i : ℕ} {F : LPol α k K} (hF : lapP a b F = 0) : pi0 k K a b u i F = F := by
  rw [pi0_eq, rho_apply, Finset.sum_eq_zero fun r _ => by rw [pow_succ, Module.End.mul_apply, hF, map_zero,
    mul_zero, smul_zero], mul_zero, add_zero]

/-- **The harmonic projection is harmonic**: `Δπ₀F = 0` on the step `i` of a chain with `u = k + d₀_a + d₀_b`
(`k ≥ 2`), a telescoping sum. -/
theorem lapP_pi0 (hk : 2 ≤ k) (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i : ℕ}
    {F : LPol α k K} (hF : F ∈ LHom K (d₀ + i • pe a b)) :
    lapP a b (pi0 k K a b (k + d₀ a + d₀ b) i F) = 0 := by
  set N := k + d₀ a + d₀ b + 2 * i - 2
  set X : ℕ → LPol α k K := fun r => (lapP a b ^ r) F
  have hX : ∀ r, lapP a b (X r) = X (r + 1) := fun r => by
    simp only [X, pow_succ', Module.End.mul_apply]
  have hterm : ∀ r ∈ range i, lapP a b (cπ K N (r + 1) • (hP a b ^ (r + 1) * X (r + 1))) =
      cπ K N (r + 1) • (hP a b ^ (r + 1) * X (r + 2)) +
        (cπ K N (r + 1) * (((r + 1) * (N - r) : ℕ) : K)) • (hP a b ^ r * X (r + 1)) := fun r hr => by
    have hr := Finset.mem_range.1 hr
    have hY := lapP_pow_mem (show r + 1 ≤ i by omega) hF
    rw [map_smul, lapP_hP_pow_mul hab hY r, hX, smul_add, smul_smul,
      show k + d₀ a + d₀ b + 2 * (i - (r + 1)) + r = N - r by simp only [N]; omega]
  rw [pi0_apply, map_sum, Finset.sum_range_succ', Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hlast : X (i + 1) = 0 := lapP_pow_eq_zero h0 (Nat.lt_succ_self i) hF
  have e1 : ∑ r ∈ range i, cπ K N (r + 1) • (hP a b ^ (r + 1) * X (r + 2)) +
      lapP a b (cπ K N 0 • (hP a b ^ 0 * X 0)) = ∑ r ∈ range i, cπ K N r • (hP a b ^ r * X (r + 1)) := by
    have := Finset.sum_range_succ' (fun r => cπ K N r • (hP a b ^ r * X (r + 1))) i
    rw [Finset.sum_range_succ, hlast, mul_zero, smul_zero, add_zero] at this
    rw [this, map_smul]
    simp only [pow_zero, one_mul, hX]
  change ∑ r ∈ range i, cπ K N (r + 1) • (hP a b ^ (r + 1) * X (r + 2)) +
      ∑ r ∈ range i, (cπ K N (r + 1) * (((r + 1) * (N - r) : ℕ) : K)) • (hP a b ^ r * X (r + 1)) +
      lapP a b (cπ K N 0 • (hP a b ^ 0 * X 0)) = 0
  rw [add_right_comm, e1, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hr := Finset.mem_range.1 hr
  rw [← add_smul, cπ_succ (by simp only [N]; omega), zero_smul]

/-- **The harmonic projection kills multiples of `h`.** -/
theorem pi0_hP_mul (hk : 2 ≤ k) (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i : ℕ}
    {Y : LPol α k K} (hY : Y ∈ LHom K (d₀ + i • pe a b)) :
    pi0 k K a b (k + d₀ a + d₀ b) (i + 1) (hP a b * Y) = 0 := by
  have hhY : hP a b * Y ∈ LHom K (d₀ + (i + 1) • pe a b) := by
    rw [add_smul, one_smul, ← add_assoc]; exact hP_mul_mem a b hY
  have hZ := lapP_pi0 hk hab h0 hhY
  rw [pi0_eq, ← mul_add] at hZ ⊢
  have hY' : Y + rho k K a b (k + d₀ a + d₀ b) (i + 1) (hP a b * Y) ∈ LHom K (d₀ + i • pe a b) :=
    add_mem hY (rho_mem hhY)
  rw [eq_zero_of_lapP_hP (by omega) hab h0 hY' hZ, mul_zero]

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **The harmonic pieces**, unfolded. -/
theorem fj_apply (u i j : ℕ) (F : LPol α k K) :
    fj k K a b u i j F = cf K (u + 2 * i - j - 1) j • pi0 k K a b u (i - j) ((lapP a b ^ j) F) := rfl

omit [Fintype α] [CharZero K] in
/-- **The harmonic pieces keep the chain**: `f_j` maps the step `i` to the step `i − j`. -/
theorem fj_mem {d₀ : α → ℕ} {u i j : ℕ} (hj : j ≤ i) {F : LPol α k K} (hF : F ∈ LHom K (d₀ + i • pe a b)) :
    fj k K a b u i j F ∈ LHom K (d₀ + (i - j) • pe a b) :=
  Submodule.smul_mem _ _ (pi0_mem (lapP_pow_mem hj hF))

/-- **The harmonic pieces are harmonic.** -/
theorem lapP_fj (hk : 2 ≤ k) (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i j : ℕ} (hj : j ≤ i)
    {F : LPol α k K} (hF : F ∈ LHom K (d₀ + i • pe a b)) :
    lapP a b (fj k K a b (k + d₀ a + d₀ b) i j F) = 0 := by
  rw [fj_apply, map_smul, lapP_pi0 hk hab h0 (lapP_pow_mem hj hF), smul_zero]

/-- **The recursion of the pieces**: `f_{j+1}(F) = f_j(−ρF)` from the step `i + 1` to the step `i`. -/
theorem fj_succ (hk : 2 ≤ k) (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) {i j : ℕ} (hj : j ≤ i)
    {F : LPol α k K} (hF : F ∈ LHom K (d₀ + (i + 1) • pe a b)) :
    fj k K a b (k + d₀ a + d₀ b) (i + 1) (j + 1) F =
      fj k K a b (k + d₀ a + d₀ b) i j (-rho k K a b (k + d₀ a + d₀ b) (i + 1) F) := by
  set u := k + d₀ a + d₀ b
  set G := -rho k K a b u (i + 1) F
  have hG : G ∈ LHom K (d₀ + i • pe a b) := neg_mem (rho_mem hF)
  have hFG : F = pi0 k K a b u (i + 1) F + hP a b * G := by
    rw [pi0_eq, mul_neg, add_neg_cancel_right]
  have hπ : (lapP a b ^ (j + 1)) (pi0 k K a b u (i + 1) F) = 0 := by
    rw [pow_succ, Module.End.mul_apply, lapP_pi0 hk hab h0 hF, map_zero]
  have hL : (lapP a b ^ (j + 1)) F = hP a b * (lapP a b ^ (j + 1)) G +
      (((j + 1 : ℕ) : K) * (((u + 2 * i : ℕ) : K) - j)) • (lapP a b ^ j) G := by
    conv_lhs => rw [hFG]
    rw [map_add, hπ, zero_add, lapP_pow_hP_mul hab h0 hG j]
  have hK : pi0 k K a b u (i - j) (hP a b * (lapP a b ^ (j + 1)) G) = 0 := by
    rcases Nat.lt_or_ge j i with hji | hji
    · have hm := lapP_pow_mem (show j + 1 ≤ i by omega) hG
      rw [show i - j = (i - (j + 1)) + 1 by omega]
      exact pi0_hP_mul hk hab h0 hm
    · rw [lapP_pow_eq_zero h0 (show i < j + 1 by omega) hG, mul_zero, map_zero]
  have hM : ((u + 2 * i : ℕ) : K) - j = ((u + 2 * i - j : ℕ) : K) := by
    rw [Nat.cast_sub (by omega)]
  rw [fj_apply, fj_apply, show i + 1 - (j + 1) = i - j by omega, hL, map_add, hK, zero_add, map_smul,
    smul_smul, hM, show u + 2 * (i + 1) - (j + 1) - 1 = u + 2 * i - j by omega,
    cf_succ (show j < u + 2 * i - j by omega), show u + 2 * i - j - 1 = u + 2 * i - j - 1 from rfl]

/-- **The harmonic decomposition** on the step `i` of a chain (`k ≥ 2`): `F = Σ_{j ≤ i} h^j·f_j(F)`. -/
theorem sum_fj (hk : 2 ≤ k) (hab : a ≠ b) {d₀ : α → ℕ} (h0 : d₀ a = 0 ∨ d₀ b = 0) :
    ∀ (i : ℕ) (F : LPol α k K), F ∈ LHom K (d₀ + i • pe a b) →
      ∑ j ∈ range (i + 1), hP a b ^ j * fj k K a b (k + d₀ a + d₀ b) i j F = F := by
  intro i
  induction i with
  | zero =>
    intro F hF
    rw [zero_smul, add_zero] at hF
    simp [fj_apply, cf_zero, pi0_apply, cπ_zero]
  | succ i ih =>
    intro F hF
    rw [Finset.sum_range_succ', Finset.sum_congr rfl fun j hj =>
      by rw [fj_succ hk hab h0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hF], pow_zero, one_mul]
    have e : ∀ j, hP a b ^ (j + 1) * fj k K a b (k + d₀ a + d₀ b) i j (-rho k K a b (k + d₀ a + d₀ b) (i + 1) F) =
        hP a b * (hP a b ^ j * fj k K a b (k + d₀ a + d₀ b) i j (-rho k K a b (k + d₀ a + d₀ b) (i + 1) F)) :=
      fun j => by rw [pow_succ', mul_assoc]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, ih _ (neg_mem (rho_mem hF)), fj_apply,
      cf_zero, one_smul, Nat.sub_zero, pow_zero, Module.End.one_apply, pi0_eq, mul_neg]
    abel

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **The harmonic pieces, expanded**: `f_j = Σ_{r ≤ i − j} cf·c_r·h^rΔ^{r+j}`. -/
theorem fj_eq_sum (u i j : ℕ) (F : LPol α k K) :
    fj k K a b u i j F = ∑ r ∈ range (i - j + 1), (cf K (u + 2 * i - j - 1) j * cπ K (u + 2 * (i - j) - 2) r) •
      (hP a b ^ r * (lapP a b ^ (r + j)) F) := by
  rw [fj_apply, pi0_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_smul, pow_add, Module.End.mul_apply]

end Proj

/-! ## Integrality: the divided Laplacian and the pieces -/

section Int

variable {K : Type*} [Field K] [CharZero K] (A : Subring K)

/-- **The polynomials with coefficients in a subring** `A ⊆ K`. -/
def intP (σ : Type*) : Subring (MvPolynomial σ K) where
  carrier := {F | ∀ μ, F.coeff μ ∈ A}
  mul_mem' {F G} hF hG μ := by
    classical
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => mul_mem (hF _) (hG _)
  one_mem' μ := by
    classical
    rw [coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  add_mem' {F G} hF hG μ := by simpa using add_mem (hF μ) (hG μ)
  zero_mem' μ := by simp
  neg_mem' {F} hF μ := by simpa using neg_mem (hF μ)

variable {A} {σ : Type*}

omit [CharZero K] in
/-- **Membership in `intP`**: all coefficients in `A`. -/
theorem mem_intP {F : MvPolynomial σ K} : F ∈ intP A σ ↔ ∀ μ, F.coeff μ ∈ A := Iff.rfl

omit [CharZero K] in
/-- **Scalars of `A` keep `intP`.** -/
theorem smul_mem_intP {c : K} (hc : c ∈ A) {F : MvPolynomial σ K} (hF : F ∈ intP A σ) : c • F ∈ intP A σ :=
  fun μ => by rw [coeff_smul, smul_eq_mul]; exact mul_mem hc (hF μ)

omit [CharZero K] in
/-- **Variables lie in `intP`.** -/
theorem X_mem_intP [DecidableEq σ] (v : σ) : (X v : MvPolynomial σ K) ∈ intP A σ := fun μ => by
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

omit [CharZero K] in
/-- **Iterated derivatives**: the coefficient of `∂_v^mF` at `μ` is `(μ_v + m)↓m` times that of `F` at
`μ + m·e_v`. -/
theorem coeff_pderiv_pow (v : σ) (m : ℕ) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    (((pderiv v).toLinearMap ^ m) F).coeff μ =
      F.coeff (μ + Finsupp.single v m) * ((μ v + m).descFactorial m : K) := by
  classical
  induction m generalizing μ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, Derivation.coeFn_coe, coeff_pderiv, ih, add_assoc,
      ← Finsupp.single_add, add_comm 1 m, mul_assoc]
    congr 1
    rw [Finsupp.add_apply, Finsupp.single_eq_same, show μ v + 1 + m = μ v + (m + 1) by ring,
      Nat.descFactorial_succ, show μ v + (m + 1) - m = μ v + 1 by omega]
    push_cast
    ring

/-- **Divided powers of a derivative keep `intP`**: `∂_v^m/m!`. -/
theorem dpow_pderiv_mem (v : σ) (m : ℕ) {F : MvPolynomial σ K} (hF : F ∈ intP A σ) :
    ((m.factorial : K)⁻¹) • ((pderiv v).toLinearMap ^ m) F ∈ intP A σ := fun μ => by
  rw [coeff_smul, coeff_pderiv_pow, Nat.descFactorial_eq_factorial_mul_choose, smul_eq_mul, Nat.cast_mul]
  convert mul_mem (hF (μ + Finsupp.single v m)) (natCast_mem A ((μ v + m).choose m)) using 1
  have := Nat.cast_ne_zero (R := K).2 (Nat.factorial_ne_zero m)
  field_simp

omit [CharZero K] in
/-- **Derivatives commute.** -/
theorem pderiv_comm (v w : σ) (F : MvPolynomial σ K) :
    pderiv v (pderiv w F) = pderiv w (pderiv v F) := by
  classical
  ext μ
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv, add_right_comm μ]
  by_cases h : v = w
  · subst h; rfl
  · simp only [Finsupp.add_apply, Finsupp.single_apply, h, Ne.symm h, ite_false, add_zero]
    ring

omit [CharZero K] in
/-- **Derivatives commute**, as linear maps. -/
theorem commute_pderiv (v w : σ) :
    Commute ((pderiv v).toLinearMap : Module.End K (MvPolynomial σ K)) (pderiv w).toLinearMap :=
  LinearMap.ext fun F => pderiv_comm v w F

variable (p : ℕ)

/-- **`p^L/n ∈ A`** once `v_p(n) ≤ L`, if the integers prime to `p` are invertible in `A`. -/
theorem pow_div_mem (hp : p.Prime) (hinv : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) {n L : ℕ} (hn : n ≠ 0)
    (hL : n.factorization p ≤ L) : (p : K) ^ L / n ∈ A := by
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self n p
  have hu := Nat.not_dvd_ordCompl hp hn
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hu0 : ((n / p ^ n.factorization p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 fun h => hu (h ▸ dvd_zero p)
  have e : (p : K) ^ L / n = (p : K) ^ (L - n.factorization p) * ((n / p ^ n.factorization p : ℕ) : K)⁻¹ := by
    conv_lhs => rw [← hsplit]
    rw [Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv, mul_inv, ← mul_assoc, ← pow_sub₀ _ hp0 hL]
  rw [e]
  exact mul_mem (pow_mem (natCast_mem _ _) _) (hinv _ hu)

end Int

section LapInt

variable {α : Type*} {k : ℕ} {K : Type*} [Field K] [CharZero K] {A : Subring K}
  {p : ℕ} {a b : α}

variable (K) in
/-- **The partial Laplacian** `Δ_S = Σ_{c ∈ S} ∂_{a,c}∂_{b,c}` over a set of coordinates. -/
def lapS (a b : α) (S : Finset (Fin k)) : Module.End K (LPol α k K) :=
  ∑ c ∈ S, (pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap

omit [CharZero K] in
/-- **The full partial Laplacian** is `Δ`. -/
theorem lapS_univ : lapS K a b (Finset.univ : Finset (Fin k)) = lapP a b := rfl

omit [CharZero K] in
/-- **The one-coordinate pieces commute** with each other. -/
theorem commute_dterm (c c' : Fin k) :
    Commute ((pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap : Module.End K (LPol α k K))
      ((pderiv (a, c')).toLinearMap * (pderiv (b, c')).toLinearMap) :=
  ((commute_pderiv (K := K) (a, c) (a, c')).mul_left (commute_pderiv (b, c) (a, c'))).mul_right
    ((commute_pderiv (a, c) (b, c')).mul_left (commute_pderiv (b, c) (b, c')))

/-- **One coordinate**: `(∂_{a,c}∂_{b,c})^m/m!²` keeps `intP`. -/
theorem dterm_pow_mem (c : Fin k) (m : ℕ) {F : LPol α k K} (hF : F ∈ intP A (α × Fin k)) :
    ((m.factorial : K) ^ 2)⁻¹ • (((pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap :
      Module.End K (LPol α k K)) ^ m) F ∈ intP A (α × Fin k) := by
  rw [(commute_pderiv _ _).mul_pow, Module.End.mul_apply, sq, mul_inv, mul_smul, ← LinearMap.map_smul]
  exact dpow_pderiv_mem _ m (dpow_pderiv_mem _ m hF)

/-- **The divided partial Laplacian loses `p^{(|S| − 1)L}`**: for `S` nonempty and `⌊log_p m⌋ ≤ L`,
`p^{(|S| − 1)L}·Δ_S^m/m!²` keeps `intP` (binomial expansion over the coordinates, `v_p C(m, i) ≤ ⌊log_p m⌋`). -/
theorem lapS_pow_mem (hp : p.Prime) (hinv : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) (L : ℕ) {S : Finset (Fin k)}
    (hS : S.Nonempty) : ∀ m, Nat.log p m ≤ L → ∀ F ∈ intP A (α × Fin k),
      ((p : K) ^ ((S.card - 1) * L) / (m.factorial : K) ^ 2) • (lapS K a b S ^ m) F ∈ intP A (α × Fin k) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton c =>
    intro m _ F hF
    simpa [lapS, div_eq_mul_inv] using dterm_pow_mem c m hF
  | cons c S hc hS ih =>
    intro m hm F hF
    set D : Module.End K (LPol α k K) := (pderiv (a, c)).toLinearMap * (pderiv (b, c)).toLinearMap with hD
    set LS := lapS K a b S
    have hcomm : Commute D LS := Commute.sum_right _ _ _ fun c' _ => commute_dterm c c'
    rw [lapS, Finset.sum_cons, ← lapS, ← hD, hcomm.add_pow, LinearMap.sum_apply, Finset.smul_sum]
    refine Subring.sum_mem _ fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    have hcard : (Finset.cons c S hc).card - 1 = 1 + (S.card - 1) := by
      rw [Finset.card_cons]; have := hS.card_pos; omega
    have hC0 : (m.choose i : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
    have hfi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
    have hfmi : ((m - i).factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hfact : (m.choose i : K) * i.factorial * (m - i).factorial = m.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : i ≤ m)
    have e : ((p : K) ^ (((Finset.cons c S hc).card - 1) * L) / (m.factorial : K) ^ 2) •
        (D ^ i * LS ^ (m - i) * ((m.choose i : ℕ) : Module.End K (LPol α k K))) F =
        ((p : K) ^ L / (m.choose i : K)) • (((i.factorial : K) ^ 2)⁻¹ •
          (D ^ i) (((p : K) ^ ((S.card - 1) * L) / ((m - i).factorial : K) ^ 2) • (LS ^ (m - i)) F)) := by
      rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
        ← Nat.cast_smul_eq_nsmul K, LinearMap.map_smul, smul_smul, smul_smul, smul_smul, hcard, add_mul, one_mul,
        pow_add]
      congr 1
      rw [← hfact]
      field_simp
    rw [e]
    refine smul_mem_intP (pow_div_mem p hp hinv (Nat.choose_pos (by omega)).ne'
      ((Nat.factorization_choose_le_log).trans hm)) (dterm_pow_mem c i ?_)
    exact ih (m - i) ((Nat.log_mono_right (Nat.sub_le m i)).trans hm) F hF

/-- **The divided Laplacian loses `p^{(k − 1)L}`**: `p^{(k − 1)L}·Δ^m/m!²` keeps `intP` when `⌊log_p m⌋ ≤ L`. -/
theorem lapP_pow_mem_intP (hk : 1 ≤ k) (hp : p.Prime) (hinv : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) {L m : ℕ}
    (hm : Nat.log p m ≤ L) {F : LPol α k K} (hF : F ∈ intP A (α × Fin k)) :
    ((p : K) ^ ((k - 1) * L) / (m.factorial : K) ^ 2) • (lapP a b ^ m) F ∈ intP A (α × Fin k) := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  simpa [lapS_univ, Finset.card_univ, Fintype.card_fin] using lapS_pow_mem hp hinv L hne m hm F hF

/-- **The harmonic pieces lose at most `p^{(k + 1)L}`**: on `intP`, for `j ≤ i`, `u ≥ 2` and
`⌊log_p(u + 2i)⌋ ≤ L`, `p^{(k + 1)L}·f_j` keeps `intP`
(`f_j = Σ_r ±C(r + j, j)²/(C(M, j)C(N, r))·h^r·Δ^{r+j}/(r + j)!²`). -/
theorem fj_mem_intP (hk : 1 ≤ k) (hp : p.Prime) (hinv : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) {u i j L : ℕ}
    (hu : 2 ≤ u) (hj : j ≤ i) (hL : Nat.log p (u + 2 * i) ≤ L) {F : LPol α k K} (hF : F ∈ intP A (α × Fin k)) :
    (p : K) ^ ((k + 1) * L) • fj k K a b u i j F ∈ intP A (α × Fin k) := by
  rw [fj_eq_sum, Finset.smul_sum]
  refine Subring.sum_mem _ fun r hr => ?_
  have hr := Finset.mem_range.1 hr
  set M := u + 2 * i - j - 1
  set N := u + 2 * (i - j) - 2
  have hM : j ≤ M := by omega
  have hN : r ≤ N := by omega
  have hCM : (M.choose j : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hM).ne'
  have hCN : (N.choose r : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hN).ne'
  have hfr : (r.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero r)
  have hfj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
  have hCrj : ((r + j).choose j : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
  have hfact : ((r + j).choose j : K) * r.factorial * j.factorial = (r + j).factorial := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial r j
  have e : (p : K) ^ ((k + 1) * L) • ((cf K M j * cπ K N r) • (hP a b ^ r * (lapP a b ^ (r + j)) F)) =
      ((-1) ^ r * ((r + j).choose j : K) ^ 2 * ((p : K) ^ L / (M.choose j : K)) *
        ((p : K) ^ L / (N.choose r : K))) •
        (hP a b ^ r * (((p : K) ^ ((k - 1) * L) / ((r + j).factorial : K) ^ 2) • (lapP a b ^ (r + j)) F)) := by
    rw [mul_smul_comm, smul_smul, smul_smul]
    congr 1
    rw [cf, cπ, ← hfact, show (k + 1) * L = L + L + (k - 1) * L by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩; simp only [Nat.add_sub_cancel]; ring]
    rw [pow_add, pow_add]
    field_simp
  rw [e]
  refine smul_mem_intP ?_ (mul_mem (pow_mem (?_ : hP a b ∈ intP A (α × Fin k)) r)
    (lapP_pow_mem_intP hk hp hinv ((Nat.log_mono_right (by omega : r + j ≤ u + 2 * i)).trans hL) hF))
  · refine mul_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) r) (pow_mem (natCast_mem _ _) 2)) ?_) ?_
    · exact pow_div_mem p hp hinv (Nat.choose_pos hM).ne' ((Nat.factorization_choose_le_log).trans
        ((Nat.log_mono_right (by omega : M ≤ u + 2 * i)).trans hL))
    · exact pow_div_mem p hp hinv (Nat.choose_pos hN).ne' ((Nat.factorization_choose_le_log).trans
        ((Nat.log_mono_right (by omega : N ≤ u + 2 * i)).trans hL))
  · classical exact Subring.sum_mem _ fun c _ => mul_mem (X_mem_intP _) (X_mem_intP _)

end LapInt

/-! ## Several positions -/

section Multi

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} {K : Type*} [Field K] [CharZero K]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι → α}

/-- **Disjoint pairs of letters**: the letters `a_s`, `b_t` are pairwise distinct. -/
structure Pairs (a b : ι → α) : Prop where
  /-- the two letters of any two positions differ -/
  ne : ∀ s t, a s ≠ b t
  /-- the first letters of different positions differ -/
  inj_a : Function.Injective a
  /-- the second letters of different positions differ -/
  inj_b : Function.Injective b

/-- **The degree on the chains** `D₀ + Σ_t c_t·(e_{a_t} + e_{b_t})`. -/
def cdeg (a b : ι → α) (D₀ : α → ℕ) (c : ι → ℕ) : α → ℕ := D₀ + ∑ t, c t • pe (a t) (b t)

variable (k K) in
/-- **The projector of a list of positions** `f^{(s₁)}_{j_{s₁}} ∘ ⋯ ∘ f^{(s_n)}_{j_{s_n}}`, position `s` on the chain
with constant `u_s` and step `J_s`. -/
def piL (a b : ι → α) (u J j : ι → ℕ) : List ι → Module.End K (LPol α k K)
  | [] => 1
  | s :: l => fj k K (a s) (b s) (u s) (J s) (j s) * piL a b u J j l

variable (k K) in
/-- **The product of the pairings** `∏_{s ∈ l} h_s^{j_s}`. -/
def hProd (a b : ι → α) (j : ι → ℕ) (l : List ι) : LPol α k K := (l.map fun s => hP (a s) (b s) ^ j s).prod

/-- **The index box of a list**: `j_s ≤ J_s` on the list, `j_s = 0` off it. -/
def jBoxL (J : ι → ℕ) (l : List ι) : Finset (ι → ℕ) :=
  Fintype.piFinset fun s => if s ∈ l then range (J s + 1) else {0}

omit [Fintype α] [Fintype ι] [DecidableEq ι] in
/-- **The pairing degree of another position** vanishes on the letters of `s`. -/
theorem Pairs.pe_other (h : Pairs a b) {s t : ι} (hst : s ≠ t) :
    pe (a t) (b t) (a s) = 0 ∧ pe (a t) (b t) (b s) = 0 := by
  have h1 : a s ≠ a t := fun e => hst (h.inj_a e)
  have h2 : b s ≠ b t := fun e => hst (h.inj_b e)
  have h3 : b s ≠ a t := fun e => h.ne t s e.symm
  refine ⟨?_, ?_⟩
  · simp [pe, h1, h.ne s t]
  · simp [pe, h2, h3]

omit [Fintype α] [DecidableEq ι] in
/-- **The chain degree at the letters of `s`**: `D₀ + c_s`. -/
theorem Pairs.cdeg_apply (h : Pairs a b) (D₀ : α → ℕ) (c : ι → ℕ) (s : ι) :
    cdeg a b D₀ c (a s) = D₀ (a s) + c s ∧ cdeg a b D₀ c (b s) = D₀ (b s) + c s := by
  simp only [cdeg, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩ <;> rw [Finset.sum_eq_single s (fun t _ hts => by
    simp [(h.pe_other (Ne.symm hts)).1, (h.pe_other (Ne.symm hts)).2]) (by simp)]
  · rw [pe_left (h.ne s s), mul_one]
  · rw [pe_right (h.ne s s), mul_one]

omit [Fintype α] in
/-- **Splitting off a position**: `cdeg c = D₀^{(s)} + c_s·pe_s`, with `D₀^{(s)}` equal to `D₀` at the letters
of `s`. -/
theorem cdeg_split (D₀ : α → ℕ) (c : ι → ℕ) (s : ι) :
    cdeg a b D₀ c = cdeg a b D₀ (Function.update c s 0) + c s • pe (a s) (b s) := by
  simp only [cdeg]
  rw [add_assoc, ← Finset.sum_erase_add _ _ (Finset.mem_univ s), ← Finset.sum_erase_add _ _ (Finset.mem_univ s),
    Function.update_self, zero_smul, add_zero]
  congr 2
  exact Finset.sum_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]

omit [Fintype α] in
/-- **The bottom of a position**: `cdeg (c with c_s = 0)` at the letters of `s` is `D₀`. -/
theorem Pairs.cdeg_update_zero (h : Pairs a b) (D₀ : α → ℕ) (c : ι → ℕ) (s : ι) :
    cdeg a b D₀ (Function.update c s 0) (a s) = D₀ (a s) ∧
      cdeg a b D₀ (Function.update c s 0) (b s) = D₀ (b s) := by
  have := h.cdeg_apply D₀ (Function.update c s 0) s
  simpa using this

omit [Fintype α] in
/-- **The chain degree after moving one position** to step `i`. -/
theorem cdeg_update (D₀ : α → ℕ) (c : ι → ℕ) (s : ι) (i : ℕ) :
    cdeg a b D₀ (Function.update c s i) = cdeg a b D₀ (Function.update c s 0) + i • pe (a s) (b s) := by
  rw [cdeg_split D₀ (Function.update c s i) s, Function.update_idem, Function.update_self]

omit [Fintype α] [CharZero K] in
/-- **A derivative in another letter passes `h^r`.** -/
theorem pderiv_hP_pow_mul {a' b' l : α} (ha : l ≠ a') (hb : l ≠ b') (c : Fin k) (r : ℕ) (G : LPol α k K) :
    pderiv (l, c) (hP a' b' ^ r * G) = hP a' b' ^ r * pderiv (l, c) G := by
  rw [pderiv_mul, pderiv_pow, pderiv_hP_other ha hb, mul_zero, zero_mul, zero_add]

omit [Fintype α] [CharZero K] in
/-- **The Laplacian of another pair passes `h^r`.** -/
theorem lapP_hP_pow_mul_other {a b a' b' : α} (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b') (r : ℕ)
    (G : LPol α k K) : lapP a b (hP a' b' ^ r * G) = hP a' b' ^ r * lapP a b G := by
  rw [lapP_apply, lapP_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [pderiv_hP_pow_mul h3 h4, pderiv_hP_pow_mul h1 h2]

omit [Fintype α] [DecidableEq α] [CharZero K] in
/-- **Pair Laplacians commute.** -/
theorem commute_lapP (a b a' b' : α) :
    Commute (lapP a b : Module.End K (LPol α k K)) (lapP a' b') :=
  Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ =>
    ((commute_pderiv (K := K) (a, c) (a', c')).mul_left (commute_pderiv (b, c) (a', c'))).mul_right
      ((commute_pderiv (a, c) (b', c')).mul_left (commute_pderiv (b, c) (b', c')))

omit [Fintype α] [CharZero K] [Fintype ι] [DecidableEq ι] in
/-- **The Laplacian of another position commutes with a piece.** -/
theorem Pairs.lapP_fj (h : Pairs a b) {s t : ι} (hst : s ≠ t) (u i j : ℕ) (F : LPol α k K) :
    lapP (a t) (b t) (fj k K (a s) (b s) u i j F) = fj k K (a s) (b s) u i j (lapP (a t) (b t) F) := by
  have h1 : a t ≠ a s := fun e => hst (h.inj_a e).symm
  have h4 : b t ≠ b s := fun e => hst (h.inj_b e).symm
  rw [fj_eq_sum, fj_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, lapP_hP_pow_mul_other h1 (h.ne t s) (fun e => h.ne s t e.symm) h4, ← Module.End.mul_apply,
    ((commute_lapP (K := K) (k := k) _ _ _ _).pow_right (r + j)).eq, Module.End.mul_apply]

omit [Fintype α] [CharZero K] in
/-- **The degree after the projector of a list** (`l` without repetitions, `J = c` on `l`, `j ≤ J`). -/
theorem piL_mem (D₀ : α → ℕ) (u J j : ι → ℕ) :
    ∀ (l : List ι), l.Nodup → ∀ (c : ι → ℕ) (F : LPol α k K), F ∈ LHom K (cdeg a b D₀ c) →
      (∀ s ∈ l, J s = c s ∧ j s ≤ J s) →
      piL k K a b u J j l F ∈ LHom K (cdeg a b D₀ fun s => if s ∈ l then c s - j s else c s) := by
  intro l
  induction l with
  | nil => intro _ c F hF _; simpa [piL] using hF
  | cons s l ih =>
    intro hl c F hF hJ
    have hsl := (List.nodup_cons.1 hl).1
    have hX := ih (List.nodup_cons.1 hl).2 c F hF fun t ht => hJ t (List.mem_cons_of_mem s ht)
    set c' : ι → ℕ := fun t => if t ∈ l then c t - j t else c t
    have hc's : c' s = J s := by simp [c', hsl, (hJ s (List.mem_cons_self)).1]
    rw [cdeg_split D₀ c' s, hc's] at hX
    have hm := fj_mem (u := u s) (hJ s List.mem_cons_self).2 hX
    rw [← cdeg_update D₀ c' s] at hm
    simp only [piL, Module.End.mul_apply]
    convert hm using 3
    funext t
    by_cases hts : t = s
    · subst hts; simp [c', hsl, (hJ t List.mem_cons_self).1]
    · simp [c', hts]

/-- **The projector of a list is harmonic** at the positions of the list. -/
theorem Pairs.lapP_piL (hk : 2 ≤ k) (h : Pairs a b) (D₀ : α → ℕ) (h0 : ∀ s, D₀ (a s) = 0 ∨ D₀ (b s) = 0)
    (J j : ι → ℕ) : ∀ (l : List ι), l.Nodup → ∀ (c : ι → ℕ) (F : LPol α k K), F ∈ LHom K (cdeg a b D₀ c) →
      (∀ s ∈ l, J s = c s ∧ j s ≤ J s) → ∀ t ∈ l,
        lapP (a t) (b t) (piL k K a b (fun s => k + D₀ (a s) + D₀ (b s)) J j l F) = 0 := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ t ht; simp at ht
  | cons s l ih =>
    intro hl c F hF hJ t ht
    have hsl := (List.nodup_cons.1 hl).1
    have hJ' : ∀ t ∈ l, J t = c t ∧ j t ≤ J t := fun t ht => hJ t (List.mem_cons_of_mem s ht)
    simp only [piL, Module.End.mul_apply]
    rcases List.mem_cons.1 ht with rfl | ht'
    · have hX := piL_mem D₀ (fun s => k + D₀ (a s) + D₀ (b s)) J j l (List.nodup_cons.1 hl).2 c F hF hJ'
      set c' : ι → ℕ := fun t => if t ∈ l then c t - j t else c t
      have hc's : c' t = J t := by simp [c', hsl, (hJ t ht).1]
      rw [cdeg_split D₀ c' t, hc's] at hX
      have hb := h.cdeg_update_zero D₀ c' t
      have := HarmDecomp.lapP_fj hk (h.ne t t) (Or.imp (fun e => hb.1.trans e) (fun e => hb.2.trans e) (h0 t))
        (hJ t ht).2 hX
      rwa [hb.1, hb.2] at this
    · have hts : s ≠ t := fun e => hsl (e ▸ ht')
      rw [h.lapP_fj hts, ih (List.nodup_cons.1 hl).2 c F hF hJ' t ht', map_zero]

/-- **Reindexing the box of `s :: l`** over the box of `l` and the range at `s`. -/
theorem sum_jBoxL_cons {M : Type*} [AddCommMonoid M] (J : ι → ℕ) {s : ι} {l : List ι} (hs : s ∉ l)
    (G : (ι → ℕ) → M) :
    ∑ j ∈ jBoxL J (s :: l), G j = ∑ j ∈ jBoxL J l, ∑ i ∈ range (J s + 1), G (Function.update j s i) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij' (fun j => (Function.update j s 0, j s)) (fun x => Function.update x.1 s x.2)
    ?_ ?_ ?_ ?_ ?_).trans rfl
  · intro j hj
    simp only [jBoxL, Fintype.mem_piFinset, Finset.mem_product] at hj ⊢
    refine ⟨fun t => ?_, ?_⟩
    · by_cases hts : t = s
      · subst hts; simp [hs]
      · rw [Function.update_of_ne hts]
        have := hj t
        simpa [hts] using this
    · simpa using hj s
  · intro x hx
    simp only [jBoxL, Fintype.mem_piFinset, Finset.mem_product] at hx ⊢
    intro t
    by_cases hts : t = s
    · subst hts; simpa using hx.2
    · rw [Function.update_of_ne hts]
      have := hx.1 t
      simpa [hts] using this
  · intro j hj
    simp
  · intro x hx
    simp only [jBoxL, Fintype.mem_piFinset, Finset.mem_product] at hx
    have h0 := hx.1 s
    simp only [hs, ite_false, Finset.mem_singleton] at h0
    ext1
    · funext t; by_cases hts : t = s
      · subst hts; simp [h0]
      · simp [Function.update_of_ne hts]
    · simp
  · intro j hj
    simp

omit [Fintype α] [DecidableEq α] [CharZero K] [Fintype ι] [DecidableEq ι] in
/-- **The projector of a list ignores the indices off the list.** -/
theorem piL_congr (u J : ι → ℕ) {j j' : ι → ℕ} (l : List ι) (h : ∀ s ∈ l, j s = j' s) :
    piL k K a b u J j l = piL k K a b u J j' l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [piL, h s List.mem_cons_self, ih fun t ht => h t (List.mem_cons_of_mem s ht)]

omit [Fintype α] [DecidableEq α] [CharZero K] [Fintype ι] [DecidableEq ι] in
/-- **The product of pairings ignores the indices off the list.** -/
theorem hProd_congr {j j' : ι → ℕ} (l : List ι) (h : ∀ s ∈ l, j s = j' s) :
    hProd k K a b j l = hProd k K a b j' l := by
  simp only [hProd]
  congr 1
  exact List.map_congr_left fun s hs => by rw [h s hs]

/-- **The harmonic decomposition at several positions** (`k ≥ 2`): for `F` of chain degree `cdeg D₀ c`, `l` without
repetitions and `J = c` on `l`: `F = Σ_{j ∈ jBoxL J l} (∏_{s ∈ l} h_s^{j_s})·π_j(F)`. -/
theorem Pairs.sum_piL (hk : 2 ≤ k) (h : Pairs a b) (D₀ : α → ℕ) (h0 : ∀ s, D₀ (a s) = 0 ∨ D₀ (b s) = 0)
    (J : ι → ℕ) : ∀ (l : List ι), l.Nodup → ∀ (c : ι → ℕ) (F : LPol α k K), F ∈ LHom K (cdeg a b D₀ c) →
      (∀ s ∈ l, J s = c s) →
      ∑ j ∈ jBoxL J l, hProd k K a b j l * piL k K a b (fun s => k + D₀ (a s) + D₀ (b s)) J j l F = F := by
  intro l
  induction l with
  | nil =>
    intro _ c F _ _
    have : jBoxL J ([] : List ι) = {0} := by
      ext j; simp [jBoxL, funext_iff]
    simp [this, hProd, piL]
  | cons s l ih =>
    intro hl c F hF hJ
    have hsl := (List.nodup_cons.1 hl).1
    rw [sum_jBoxL_cons J hsl]
    conv_rhs => rw [← ih (List.nodup_cons.1 hl).2 c F hF fun t ht => hJ t (List.mem_cons_of_mem s ht)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : j s = 0 := by
      have := Fintype.mem_piFinset.1 hj s
      simpa [hsl] using this
    have hX := piL_mem D₀ (fun s => k + D₀ (a s) + D₀ (b s)) J j l (List.nodup_cons.1 hl).2 c F hF
      fun t ht => ⟨hJ t (List.mem_cons_of_mem s ht), by
        have := Fintype.mem_piFinset.1 hj t; simp only [ht, ite_true, Finset.mem_range] at this; omega⟩
    set c' : ι → ℕ := fun t => if t ∈ l then c t - j t else c t
    have hc's : c' s = J s := by simp [c', hsl, hJ s List.mem_cons_self]
    rw [cdeg_split D₀ c' s, hc's] at hX
    have hb := h.cdeg_update_zero D₀ c' s
    have hdec := sum_fj (K := K) hk (h.ne s s) (Or.imp (fun e => hb.1.trans e) (fun e => hb.2.trans e) (h0 s))
      (J s) _ hX
    rw [hb.1, hb.2] at hdec
    have e : ∀ i ∈ range (J s + 1), hProd k K a b (Function.update j s i) (s :: l) *
        piL k K a b (fun s => k + D₀ (a s) + D₀ (b s)) J (Function.update j s i) (s :: l) F =
        hProd k K a b j l * (hP (a s) (b s) ^ i * fj k K (a s) (b s) (k + D₀ (a s) + D₀ (b s)) (J s) i
          (piL k K a b (fun s => k + D₀ (a s) + D₀ (b s)) J j l F)) := fun i _ => by
      have hl' : ∀ t ∈ l, Function.update j s i t = j t := fun t ht =>
        Function.update_of_ne (fun e : t = s => hsl (e ▸ ht)) _ _
      simp only [hProd, List.map_cons, List.prod_cons, piL, Module.End.mul_apply, Function.update_self]
      rw [← hProd, ← hProd, hProd_congr l hl', piL_congr _ _ l hl']
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hdec]

end Multi

/-! ## Several positions: integrality, the kernel of `h` and letter changes -/

section MultiMore

variable {α : Type*} [DecidableEq α] {k : ℕ} {K : Type*} [Field K] [CharZero K]
  {ι : Type*} {a b : ι → α}

omit [DecidableEq α] in
/-- **The projector of a list loses `p^{Σ_s (k + 1)L_s}`** on `intP`, if at each position of the list `u_s ≥ 2`,
`j_s ≤ J_s` and `⌊log_p(u_s + 2J_s)⌋ ≤ L_s`. -/
theorem piL_mem_intP {A : Subring K} {p : ℕ} (hk : 1 ≤ k) (hp : p.Prime)
    (hinv : ∀ m : ℕ, ¬ p ∣ m → (m : K)⁻¹ ∈ A) (u J j L : ι → ℕ) :
    ∀ l : List ι, (∀ s ∈ l, 2 ≤ u s ∧ j s ≤ J s ∧ Nat.log p (u s + 2 * J s) ≤ L s) →
      ∀ F ∈ intP A (α × Fin k),
        (p : K) ^ (l.map fun s => (k + 1) * L s).sum • piL k K a b u J j l F ∈ intP A (α × Fin k) := by
  intro l
  induction l with
  | nil => intro _ F hF; simpa [piL] using hF
  | cons s l ih =>
    intro hl F hF
    obtain ⟨hu, hj, hL⟩ := hl s List.mem_cons_self
    simp only [piL, List.map_cons, List.sum_cons, Module.End.mul_apply, pow_add, mul_smul]
    rw [← LinearMap.map_smul]
    exact fj_mem_intP hk hp hinv hu hj hL (ih (fun t ht => hl t (List.mem_cons_of_mem s ht)) F hF)

omit [DecidableEq α] [CharZero K] in
/-- **The piece `f_0` is the harmonic projection.** -/
theorem fj_zero (a' b' : α) (u i : ℕ) : fj k K a' b' u i 0 = pi0 k K a' b' u i := by
  refine LinearMap.ext fun F => ?_
  rw [fj_apply, cf_zero, one_smul, Nat.sub_zero, pow_zero, Module.End.one_apply]

omit [DecidableEq α] [CharZero K] in
/-- **Algebra maps killing the pairings ignore `π_0`**: `β(π_0F) = β(F)` if `β(h_s) = 0` on the list. -/
theorem map_piL_zero {S : Type*} [CommRing S] [Algebra K S] (β : LPol α k K →ₐ[K] S) (u J : ι → ℕ) :
    ∀ l : List ι, (∀ s ∈ l, β (hP (a s) (b s)) = 0) → ∀ F, β (piL k K a b u J 0 l F) = β F := by
  intro l
  induction l with
  | nil => intro _ F; rfl
  | cons s l ih =>
    intro hl F
    simp only [piL, Module.End.mul_apply, Pi.zero_apply, fj_zero, pi0_eq, map_add, map_mul,
      hl s List.mem_cons_self, zero_mul, add_zero]
    exact ih (fun t ht => hl t (List.mem_cons_of_mem s ht)) F

omit [DecidableEq α] [CharZero K] in
/-- **`π_0` fixes polynomials harmonic at every position of the list.** -/
theorem piL_zero_of_lapP (u J : ι → ℕ) :
    ∀ l : List ι, ∀ F : LPol α k K, (∀ s ∈ l, lapP (a s) (b s) F = 0) → piL k K a b u J 0 l F = F := by
  intro l
  induction l with
  | nil => intro F _; rfl
  | cons s l ih =>
    intro F hF
    simp only [piL, Module.End.mul_apply, Pi.zero_apply, fj_zero]
    rw [ih F fun t ht => hF t (List.mem_cons_of_mem s ht), pi0_of_lapP (hF s List.mem_cons_self)]

variable (k) in
/-- **The letter change** `X_{l,c} ↦ Σ_e A_l(c, e)·X_{l,e}` (`LetterFock.linSub` for any letters). -/
def linS (A : α → Matrix (Fin k) (Fin k) K) : LPol α k K →ₐ[K] LPol α k K :=
  aeval fun v => ∑ e, C (A v.1 v.2 e) * X (v.1, e)

omit [DecidableEq α] [CharZero K] in
/-- **The letter change on a variable.** -/
theorem linS_X (A : α → Matrix (Fin k) (Fin k) K) (l : α) (c : Fin k) :
    linS k A (X (l, c)) = ∑ e, C (A l c e) * X (l, e) := aeval_X _ _

omit [DecidableEq α] [CharZero K] in
/-- **The letter change on the pairing**: `γ·h` when `A_aᵀA_b = γ·1`. -/
theorem linS_hP (A : α → Matrix (Fin k) (Fin k) K) {a' b' : α} {γ : K}
    (hA : (A a')ᵀ * A b' = γ • (1 : Matrix (Fin k) (Fin k) K)) : linS k A (hP a' b') = γ • hP a' b' := by
  have hδ : ∀ e f, ∑ c, (C (A a' c e * A b' c f) : LPol α k K) = C (if e = f then γ else 0) := fun e f => by
    rw [← map_sum]
    congr 1
    have h := congrFun (congrFun hA e) f
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc linS k A (hP a' b') = ∑ e, ∑ f, ∑ c, C (A a' c e * A b' c f) * (X (a', e) * X (b', f)) := by
        simp only [hP, map_sum, map_mul, linS_X, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = γ • hP a' b' := by
        simp only [← Finset.sum_mul, hδ, hP, Finset.smul_sum, smul_eq_C_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_eq_single e (fun f _ hf => by simp [Ne.symm hf]) (by simp)]
        simp

omit [CharZero K] in
/-- **The chain rule for a letter change**: `∂_{l,c'}(F∘A) = Σ_c A_l(c, c')·(∂_{l,c}F)∘A`. -/
theorem pderiv_linS (A : α → Matrix (Fin k) (Fin k) K) (l : α) (c' : Fin k) (F : LPol α k K) :
    pderiv (l, c') (linS k A F) = ∑ c, C (A l c c') * linS k A (pderiv (l, c) F) := by
  induction F using MvPolynomial.induction_on with
  | C x => simp
  | add F G hF hG => simp only [map_add, hF, hG, mul_add, Finset.sum_add_distrib]
  | mul_X F v hF =>
    obtain ⟨l', e⟩ := v
    have h1 : pderiv (l, c') (linS k A (X (l', e))) = if l' = l then C (A l e c') else 0 := by
      rw [linS_X, map_sum]
      simp only [pderiv_mul, pderiv_C, zero_mul, zero_add, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hl : l' = l
      · subst hl; simp
      · simp [hl]
    have h2 : ∀ c, linS k A (pderiv (l, c) (X (l', e))) = if l' = l ∧ e = c then 1 else 0 := fun c => by
      rw [pderiv_X, Pi.single_apply]
      split_ifs <;> simp_all
    rw [map_mul, pderiv_mul, hF, h1]
    simp only [pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib, h2]
    congr 1
    · rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    · by_cases hl : l' = l
      · subst hl
        rw [Finset.sum_eq_single e (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
        simp only [and_self, ite_true, mul_one]
        ring
      · simp [hl]

omit [CharZero K] in
/-- **The pair Laplacian after a letter change**: `Δ(F∘A) = γ·(ΔF)∘A` when `A_aA_bᵀ = γ·1`. -/
theorem lapP_linS (A : α → Matrix (Fin k) (Fin k) K) {a' b' : α} {γ : K}
    (hA : A a' * (A b')ᵀ = γ • (1 : Matrix (Fin k) (Fin k) K)) (F : LPol α k K) :
    lapP a' b' (linS k A F) = γ • linS k A (lapP a' b' F) := by
  have hδ : ∀ e c, ∑ c', (C (A a' e c' * A b' c c') : LPol α k K) = C (if e = c then γ else 0) := fun e c => by
    rw [← map_sum]
    congr 1
    have h := congrFun (congrFun hA e) c
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc lapP a' b' (linS k A F) =
        ∑ c, ∑ e, ∑ c', C (A a' e c' * A b' c c') * linS k A (pderiv (a', e) (pderiv (b', c) F)) := by
        simp only [lapP_apply, pderiv_linS, map_sum, pderiv_C_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul]
        ring
    _ = γ • linS k A (lapP a' b' F) := by
        simp only [← Finset.sum_mul, hδ, lapP_apply, map_sum, Finset.smul_sum, smul_eq_C_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_eq_single c (fun e _ he => by simp [he]) (by simp)]
        simp

/-- **The conditions on the letter matrices at a position**: `A_aᵀA_b = A_aA_bᵀ = γ·1`. -/
def LetCond (A : α → Matrix (Fin k) (Fin k) K) (a' b' : α) (γ : K) : Prop :=
  (A a')ᵀ * A b' = γ • (1 : Matrix (Fin k) (Fin k) K) ∧ A a' * (A b')ᵀ = γ • (1 : Matrix (Fin k) (Fin k) K)

omit [CharZero K] in
/-- **The pieces after a letter change**: `f_j(F∘A) = γ^j·f_j(F)∘A`. -/
theorem fj_linS (A : α → Matrix (Fin k) (Fin k) K) {a' b' : α} {γ : K} (hA : LetCond A a' b' γ)
    (u i j : ℕ) (F : LPol α k K) :
    fj k K a' b' u i j (linS k A F) = γ ^ j • linS k A (fj k K a' b' u i j F) := by
  have hpow : ∀ m G, (lapP a' b' ^ m) (linS k A G) = γ ^ m • linS k A ((lapP a' b' ^ m) G) := fun m => by
    induction m with
    | zero => intro G; simp
    | succ m ih =>
      intro G
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, lapP_linS A hA.2, smul_smul, ← pow_succ,
        Module.End.mul_apply, pow_succ']
  rw [fj_eq_sum, fj_eq_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hpow, mul_smul_comm, smul_smul, map_smul, map_mul, map_pow, linS_hP A hA.1, smul_pow, smul_mul_assoc,
    smul_smul, smul_smul, pow_add]
  congr 1
  ring

omit [CharZero K] in
/-- **The projector of a list after a letter change**: `π_j(F∘A) = (∏_{s ∈ l} γ_s^{j_s})·π_j(F)∘A`. -/
theorem piL_linS (A : α → Matrix (Fin k) (Fin k) K) {γ : ι → K} (u J j : ι → ℕ) :
    ∀ l : List ι, (∀ s ∈ l, LetCond A (a s) (b s) (γ s)) → ∀ F,
      piL k K a b u J j l (linS k A F) = (l.map fun s => γ s ^ j s).prod • linS k A (piL k K a b u J j l F) := by
  intro l
  induction l with
  | nil => intro _ F; simp [piL]
  | cons s l ih =>
    intro hl F
    simp only [piL, Module.End.mul_apply, List.map_cons, List.prod_cons]
    rw [ih (fun t ht => hl t (List.mem_cons_of_mem s ht)), LinearMap.map_smul,
      fj_linS A (hl s List.mem_cons_self), smul_smul, mul_comm]

end MultiMore

end

end HarmDecomp
