import SymbolData
import TwistedDegree

/-!
# The source keys of the second local theorem: Frobenius alignment, keys and the localiser (L6 N8, C1–C3)

The explicit polynomials of N8 (the realisation machinery of L6 at the main edge, `p < p₀`) and their behaviour under
the adapted substitution `Φ_g = liftSub … g` of `LetterFock`: at `g = 1` (the main edge) and at every `g′ ∈ GL_k(W)`,
in particular off the main plane.

**Conventions** (those of `LetterFock`, `LocalOrbit` and `SymbolData`). The flat letters are `LPol (Fin n′) (r + K)`,
`k = r + K`, columns `c < r` the plane, `c ≥ r` the normal ones, flags `vecF` (even positions vector letters, `n′`
even). The scaled variables are the normal columns at even letters and the plane columns at odd letters; `nd` is the
`ϖ`-degree, and `ϖ`-degree conditions are read as weighted homogeneity for the weight `scW`. `ord_g F ≥ i` is
`OrdGe ϖ i (Φ_g F)`; integral is `OrdGe ϖ 0`. The frames, rows and pushes are `LocalOrbit`'s; `Q_j = p^{z_{j+1} − z_j}`
(`frameQ`) and `α_j` is `SymbolData`'s `alpha`.

**The explicit polynomials** (all with integer coefficients, defined over any commutative ring `R`; variables at the
tops). `pent x e c = X_{(x mod n′, c)}^{p^e}` (a pushed entry); `Tp(j, x)` the plane determinant of the rows of `x`
pushed to `x`; the even key `κ(j, x, b)` the `(r+1)`-minor of the rows of `x` and the row `x` on the columns
`[0, r) ∪ {r + b}`; the odd key `κ(j, x, l) = Σ_c X_{x,c}·pent(rows_l, x − rows_l, c)`; `Δ_j = frameDet j` the plane
determinant of the frame `j` pushed to `z_j`, `frameMinor j I` the same rows on the columns `I`; `mixedCols` the
`r`-sets with exactly `r − 1` plane columns; the localiser
`locPoly = Δ_0·∏_{I ∈ mixedCols}(∏_{j<J} Δ_j^{Q_j−1} − ∏_{j<J} minor_{I,j}^{Q_j−1})`, its unscaled part
`locLead = ∏_j Δ_j^{α_j}`; `budgetProd = ∏_{j<J} ∏_{x ∈ late j} Tp(j, x)`, `fixFactor`, `labelBudget`.

**Main results.**
* *The order calculus* (`ordGe_add`, `ordGe_mul`, `ordGe_det`, `ordGe_prod_sub_prod`, `ordGe_det_sub`,
  `ordGe_liftSub`): orders add under products, congruent integral matrices have congruent determinants, and `Φ_g`
  keeps orders.
* *Frobenius alignment* (`pent_ad_congr`, A1): at an even letter, `Φ_{g′}(pent x e c) ≡ Σ_{b<r} σ^{x+e}(g′⁻¹)_{bc}·
  pent x e b (mod ϖ)`; so a minor of pushed rows with a common target is, modulo `ϖ`, a product through an `r`-column
  matrix (`det_ad_pushed`).
* *Keys* (`IsPlaneKey`, `keyEven_isKey`, `keyOdd_isKey`, C3): the even and odd keys of a late letter are keys of level
  `1` with leading forms `ϖ·X_{x,r+b}·Tp(j, x)` and `ϖ·Σ_{c<r} X_{x,c}·pent(rows_l, ·, c)`, small at every `g′`; the
  odd cofactor identity `ϖ·X_{x,c}·Tp = Σ_l adj(P)_{c,l}·κ₀_l` (`odd_cofactor_identity`).
* *The localiser off the plane* (`locPoly_offPlane`, C1): `ord_{g′}(locPoly) ≥ 1` for `g′` off the main plane.
* *The localiser at the plane* (`locPoly_sub_locLead`, C2): `locLead` is unscaled and every monomial of
  `locPoly − locLead` is scaled; integrality and supports (`explicit_int`).

**The routes.** Frobenius alignment is the binomial theorem, the freshman's dream over `O[X]`
(`TwistedDegree.sum_pow_prime_pow`) and `σ^e(t) ≡ t^{p^e}` (`frob_pow`), with `σ^{n′} = 1` to read the exponent mod
`n′`. Keys at `g = 1`: Laplace along the normal column (the other entries are `ϖ^{p^e}`-scaled, `p^e ≥ 2`); smallness:
every row is pushed to the same target `x`, so the matrix is `≡ U·M` with `U` of size `(r+1) × r` (`det_mul_eq_zero_of_
succ`), resp. `Σ_c σ^x(g′)_{cb}·σ^x(g′⁻¹)_{b′c} = δ` for the odd key. The localiser: each frame minor is
`≡ Δ_j·σ^{z_j}(det N_I)` (`frame_congr`), `N` the first `r` rows of `g′⁻¹`; if `det N_{[0,r)} ≡ 0 (mod p)` the factor
`Δ_0` vanishes; otherwise off the plane some normal entry of `N` is a unit mod `p` (`planeOf_eq_one`), so some mixed
minor is a unit (`exists_mixed_minor`, on the row-reduced matrix `N_{[0,r)}⁻¹N`), and by telescoping
`∏_j σ^{z_j}(y)^{Q_j−1} ≡ 1` for units `y` (`tele_unit`, `tele_tau`: `σ^{z_j}(y)^{Q_j} ≡ σ^{z_{j+1}}(y)` and
`z_{j+J} = z_j + n′`) both products of that factor agree mod `p`. At the plane: `|mixedCols| = rK` (`card_mixedCols`),
so `locLead = Δ_0·(∏_j Δ_j^{Q_j−1})^{|mixedCols|}`, and every mixed minor lies in the ideal of scaled polynomials
(`scIdeal`, `frameMinor_mem_scIdeal`).

**Readings of the planning statements.** The spec's scaffold states the explicit polynomials over `Kf`; here over any
commutative ring (the `Kf` instances are the ones used). `locPoly_sub_locLead` and `explicit_int` need `n′` even (an
even lifted position has an even residue) and `locPoly_sub_locLead` needs `p ≥ 2` (`Q_0 − 1 ≥ 1`); both are among
L6's hypotheses. The spec's choice of `I` for the vanishing off the plane is from the row-reduced matrix, with the
degenerate case covered by `Δ_0`.
-/

namespace SourceKeys

open MvPolynomial Finset LetterFock LocalOrbit SymbolData InertModel

open scoped Matrix

noncomputable section

/-! ## The `ϖ`-order calculus -/

section Ord

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {ϖ : O} {τ : Type*}

/-- **`0` has every order.** -/
theorem ordGe_zero (i : ℕ) : OrdGe ϖ i (0 : MvPolynomial τ Kf) := fun _ => ⟨0, by simp⟩

/-- **Orders add up under sums.** -/
theorem ordGe_add {i : ℕ} {F G : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) (hG : OrdGe ϖ i G) :
    OrdGe ϖ i (F + G) := fun m => by
  obtain ⟨a, ha⟩ := hF m
  obtain ⟨b, hb⟩ := hG m
  exact ⟨a + b, by simp [ha, hb, mul_add]⟩

/-- **Order of a negative.** -/
theorem ordGe_neg {i : ℕ} {F : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) : OrdGe ϖ i (-F) := fun m => by
  obtain ⟨a, ha⟩ := hF m
  exact ⟨-a, by rw [coeff_neg, ha, ← map_neg, mul_neg]⟩

/-- **Order of a difference.** -/
theorem ordGe_sub {i : ℕ} {F G : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) (hG : OrdGe ϖ i G) :
    OrdGe ϖ i (F - G) := by
  rw [sub_eq_add_neg]
  exact ordGe_add hF (ordGe_neg hG)

/-- **A higher order is a lower order.** -/
theorem ordGe_mono {i j : ℕ} (h : j ≤ i) {F : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) : OrdGe ϖ j F := fun m => by
  obtain ⟨a, ha⟩ := hF m
  exact ⟨ϖ ^ (i - j) * a, by rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]⟩

/-- **Orders add under products.** -/
theorem ordGe_mul {i j : ℕ} {F G : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) (hG : OrdGe ϖ j G) :
    OrdGe ϖ (i + j) (F * G) := by
  classical
  intro m
  choose a ha using hF
  choose b hb using hG
  refine ⟨∑ x ∈ antidiagonal m, a x.1 * b x.2, ?_⟩
  rw [coeff_mul, mul_sum, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [ha, hb, ← map_mul]
  congr 1
  ring

/-- **Order of an integer multiple.** -/
theorem ordGe_zsmul {i : ℕ} {F : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) (n : ℤ) : OrdGe ϖ i (n • F) := fun m => by
  obtain ⟨a, ha⟩ := hF m
  exact ⟨n * a, by rw [coeff_smul, ha, zsmul_eq_mul, ← map_intCast (algebraMap O Kf), ← map_mul]; congr 1; ring⟩

/-- **Order of a finite sum.** -/
theorem ordGe_sum {ι' : Type*} {s : Finset ι'} {f : ι' → MvPolynomial τ Kf} {i : ℕ}
    (h : ∀ x ∈ s, OrdGe ϖ i (f x)) : OrdGe ϖ i (∑ x ∈ s, f x) :=
  Finset.sum_induction f (OrdGe ϖ i) (fun _ _ ha hb => ordGe_add ha hb) (ordGe_zero i) h

/-- **`1` is integral.** -/
theorem ordGe_one : OrdGe ϖ 0 (1 : MvPolynomial τ Kf) := fun m => by
  classical
  refine ⟨if 0 = m then 1 else 0, ?_⟩
  rw [coeff_one]
  split_ifs <;> simp

/-- **Variables are integral.** -/
theorem ordGe_X (v : τ) : OrdGe ϖ 0 (X v : MvPolynomial τ Kf) := fun m => by
  classical
  refine ⟨if Finsupp.single v 1 = m then 1 else 0, ?_⟩
  rw [coeff_X]
  split_ifs <;> simp

/-- **Constants from `ϖ^i·O` have order `i`.** -/
theorem ordGe_C (i : ℕ) (o : O) : OrdGe ϖ i (C (algebraMap O Kf (ϖ ^ i * o)) : MvPolynomial τ Kf) := fun m => by
  classical
  refine ⟨if 0 = m then o else 0, ?_⟩
  rw [coeff_C]
  split_ifs <;> simp

/-- **Integral constants.** -/
theorem ordGe_C_int (o : O) : OrdGe ϖ 0 (C (algebraMap O Kf o) : MvPolynomial τ Kf) := by
  simpa using ordGe_C (τ := τ) (ϖ := ϖ) 0 o

/-- **Order of a constant.** -/
theorem ordGe_C_iff {i : ℕ} {a : Kf} : OrdGe ϖ i (C a : MvPolynomial τ Kf) ↔ ∃ o : O, a = algebraMap O Kf (ϖ ^ i * o) :=
  ⟨fun h => by simpa using h 0, fun ⟨o, ho⟩ => ho ▸ ordGe_C i o⟩

/-- **Order of a finite product of integral polynomials.** -/
theorem ordGe_prod {ι' : Type*} {s : Finset ι'} {f : ι' → MvPolynomial τ Kf} (h : ∀ x ∈ s, OrdGe ϖ 0 (f x)) :
    OrdGe ϖ 0 (∏ x ∈ s, f x) :=
  Finset.prod_induction f (OrdGe ϖ 0) (fun _ _ ha hb => by simpa using ordGe_mul ha hb) ordGe_one h

/-- **Order of a power.** -/
theorem ordGe_pow {i : ℕ} {F : MvPolynomial τ Kf} (hF : OrdGe ϖ i F) (n : ℕ) : OrdGe ϖ (n * i) (F ^ n) := by
  induction n with
  | zero => simpa using ordGe_one
  | succ n ih => rw [pow_succ, Nat.succ_mul]; exact ordGe_mul ih hF

/-- **Integral determinants**: a determinant of integral entries is integral. -/
theorem ordGe_det {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix m m (MvPolynomial τ Kf)}
    (h : ∀ a b, OrdGe ϖ 0 (M a b)) : OrdGe ϖ 0 M.det := by
  rw [Matrix.det_apply]
  refine ordGe_sum fun σ' _ => ?_
  rw [Units.smul_def]
  exact ordGe_zsmul (ordGe_prod fun a _ => h _ _) _

/-- **Congruent products**: if `f ≡ g` to order `i` factorwise, with integral factors, the products are congruent. -/
theorem ordGe_prod_sub_prod {ι' : Type*} {s : Finset ι'} {f g : ι' → MvPolynomial τ Kf} {i : ℕ}
    (hf : ∀ x ∈ s, OrdGe ϖ 0 (f x)) (hg : ∀ x ∈ s, OrdGe ϖ 0 (g x)) (hfg : ∀ x ∈ s, OrdGe ϖ i (f x - g x)) :
    OrdGe ϖ i (∏ x ∈ s, f x - ∏ x ∈ s, g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ordGe_zero i
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha,
      show f a * ∏ x ∈ s, f x - g a * ∏ x ∈ s, g x =
        f a * (∏ x ∈ s, f x - ∏ x ∈ s, g x) + (f a - g a) * ∏ x ∈ s, g x by ring]
    have h1 := ordGe_mul (hf a (mem_insert_self a s)) (ih (fun x hx => hf x (mem_insert_of_mem hx))
      (fun x hx => hg x (mem_insert_of_mem hx)) (fun x hx => hfg x (mem_insert_of_mem hx)))
    have h2 := ordGe_mul (hfg a (mem_insert_self a s)) (ordGe_prod fun x hx => hg x (mem_insert_of_mem hx))
    rw [zero_add] at h1
    rw [add_zero] at h2
    exact ordGe_add h1 h2

/-- **Congruent powers.** -/
theorem ordGe_pow_sub_pow {F G : MvPolynomial τ Kf} {i : ℕ} (hF : OrdGe ϖ 0 F) (hG : OrdGe ϖ 0 G)
    (hFG : OrdGe ϖ i (F - G)) (n : ℕ) : OrdGe ϖ i (F ^ n - G ^ n) := by
  rw [← geom_sum₂_mul]
  have h := ordGe_mul (ordGe_sum (s := range n) fun x _ => by
    simpa using ordGe_mul (ordGe_pow hF x) (ordGe_pow hG (n - 1 - x))) hFG
  rwa [zero_add] at h

/-- **Congruent determinants**: entrywise congruent integral matrices have congruent determinants. -/
theorem ordGe_det_sub {m : Type*} [Fintype m] [DecidableEq m] {A B : Matrix m m (MvPolynomial τ Kf)} {i : ℕ}
    (hA : ∀ a b, OrdGe ϖ 0 (A a b)) (hB : ∀ a b, OrdGe ϖ 0 (B a b)) (hAB : ∀ a b, OrdGe ϖ i (A a b - B a b)) :
    OrdGe ϖ i (A.det - B.det) := by
  rw [Matrix.det_apply, Matrix.det_apply, ← sum_sub_distrib]
  refine ordGe_sum fun σ' _ => ?_
  rw [Units.smul_def, Units.smul_def, ← smul_sub]
  exact ordGe_zsmul (ordGe_prod_sub_prod (fun a _ => hA _ _) (fun a _ => hB _ _) fun a _ => hAB _ _) _

end Ord

/-! ## The setting: the main-edge substitution, planes, unscaled polynomials -/

section Setting

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

variable (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (ϖ : O) (n' r K : ℕ)

/-- **The adapted substitution at `g`** on the flat letters (`Φ_g`, `ℓ_g`): `liftSub` with the flat flags. -/
abbrev ad (g : Matrix (Fin (r + K)) (Fin (r + K)) W) :
    LPol (Fin n') (r + K) Kf →ₐ[Kf] LPol (Fin n') (r + K) Kf :=
  liftSub ι σ ϖ r (vecF n') (fun s => s.val) g

variable {n' r K}

/-- **Off the main plane**: `g′ ∈ GL_k(W)` whose plane differs from the plane of `1`. -/
def OffPlane (p : ℕ) (g' : Matrix (Fin (r + K)) (Fin (r + K)) W) : Prop :=
  IsUnit g'.det ∧ planeOf p r g' ≠ planeOf p r (1 : Matrix (Fin (r + K)) (Fin (r + K)) W)

variable {ι σ}

/-- **Unscaled on the tops**: integral, supported on the letters of `TT`, every monomial of `ϖ`-degree `0` (the
`h`-factors of terms; at `g = 1` they are fixed by `Φ_1`). -/
def Unscaled (TT : Finset (Fin n')) (h : LPol (Fin n') (r + K) Kf) : Prop :=
  OrdGe ϖ 0 h ∧ h ∈ supported Kf {v | v.1 ∈ TT} ∧ ∀ m ∈ h.support, nd r (vecF n') m = 0

variable {jW : W →+* O} {p : ℕ} {ϖ}

/-- **The lift substitution keeps orders**: `ord(ℓ_g F) ≥ i` when `F` has order `≥ i` (the twisted matrices are
integral). -/
theorem ordGe_liftSub (hU : Unram p n' W Qq O Kf ι σ jW ϖ) {α : Type*} {k : ℕ} (vec : α → Bool) (pos : α → ℕ)
    (g : Matrix (Fin k) (Fin k) W) {i : ℕ} {F : LPol α k Kf} (hF : OrdGe ϖ i F) :
    OrdGe ϖ i (liftSub ι σ ϖ r vec pos g F) := by
  have hϖ := LocalLattice.varpiK_ne_zero hU
  set F' := C ((algebraMap O Kf ϖ ^ i)⁻¹) * F with hF'
  have hF'i : OrdGe ϖ 0 F' := fun m => by
    obtain ⟨a, ha⟩ := hF m
    refine ⟨a, ?_⟩
    rw [hF', coeff_C_mul, ha, map_mul, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hϖ), pow_zero, one_mul,
      one_mul]
  have e : F = C (algebraMap O Kf ϖ ^ i) * F' := by
    rw [hF', ← mul_assoc, ← C_mul, mul_inv_cancel₀ (pow_ne_zero _ hϖ), C_1, one_mul]
  have hG : OrdGe ϖ 0 (liftSub ι σ ϖ r vec pos g F') := fun m => by
    obtain ⟨c, hc⟩ := liftSub_mem_gInt hU r vec pos g hF'i m
    exact ⟨ϖ ^ nd r vec m * c, by rw [hc, pow_zero, one_mul]⟩
  rw [e, map_mul, algHom_C]
  have h := ordGe_mul (ordGe_C (τ := α × Fin k) (ϖ := ϖ) i 1) hG
  rw [add_zero, mul_one, map_pow] at h
  exact h

end Setting

/-! ## The explicit polynomials: pushed rows, `Tp`, keys, the localiser -/

section Explicit

variable {n' r : ℕ} [NeZero n'] [NeZero r] (F : FrameSys n' r) (TT : Finset (Fin n')) (R : Type*) [CommRing R]
  (p K : ℕ)

/-- **A pushed entry**: `X_{(x mod n′, c)}^{p^e}`. -/
def pent (x : ℤ) (e : ℕ) (c : Fin (r + K)) : LPol (Fin n') (r + K) R := X (posOf n' x, c) ^ p ^ e

/-- **`Tp(j, x)`**: the `r × r` plane determinant of the rows of `x` (the `r` most recent even letters of `seg j`
before `x`), each pushed to `x`. -/
def Tp (j x : ℤ) : LPol (Fin n') (r + K) R :=
  (Matrix.of fun l c : Fin r =>
    pent R p K (F.rows TT j x l) (x - F.rows TT j x l).toNat (Fin.castAdd K c)).det

/-- The column map of an even key: plane columns `c < r`, then the normal column `r + b`. -/
def keyCol {K : ℕ} (b : Fin K) : Fin (r + 1) → Fin (r + K) :=
  Fin.lastCases (Fin.natAdd r b) (fun c => Fin.castAdd K c)

/-- **The even key** `κ(j, x, b)` (`x` even): the `(r+1)`-minor of the rows of `x` pushed to `x` and the row `x`
itself, on the columns `[0, r) ∪ {r + b}`. -/
def keyEven (j x : ℤ) (b : Fin K) : LPol (Fin n') (r + K) R :=
  (Matrix.of fun l c : Fin (r + 1) =>
    Fin.lastCases (pent R p K x 0 (keyCol b c))
      (fun l' : Fin r => pent R p K (F.rows TT j x l') (x - F.rows TT j x l').toNat (keyCol b c)) l).det

/-- **The odd key** `κ(j, x, l)` (`x` odd): the contraction `Σ_c X_{x,c}·X_{rows_l, c}^{p^{x − rows_l}}`. -/
def keyOdd (j x : ℤ) (l : Fin r) : LPol (Fin n') (r + K) R :=
  ∑ c : Fin (r + K), X (posOf n' x, c) * pent R p K (F.rows TT j x l) (x - F.rows TT j x l).toNat c

/-- **`Δ_j`**: the plane determinant of the frame `j`, rows pushed to `z_j`. -/
def frameDet (j : ℤ) : LPol (Fin n') (r + K) R :=
  (Matrix.of fun l c : Fin r => pent R p K (F.f j l) (F.push j (F.f j l)) (Fin.castAdd K c)).det

/-- **`minor_{I,j}`**: the same rows on the columns `I` (`|I| = r`). -/
def frameMinor (j : ℤ) (I : Finset (Fin (r + K))) : LPol (Fin n') (r + K) R :=
  if h : I.card = r then
    (Matrix.of fun l c : Fin r => pent R p K (F.f j l) (F.push j (F.f j l)) (I.orderEmbOfFin h c)).det
  else 0

/-- **`mixedCols`**: the `r`-sets of columns with exactly `r − 1` plane columns. -/
def mixedCols : Finset (Finset (Fin (r + K))) :=
  univ.filter fun I => I.card = r ∧ (I.filter fun c => c.val < r).card = r - 1

/-- **`Q_j = p^{z_{j+1} − z_j}`** (`∏_{j<J} Q_j = q`). -/
def frameQ (j : ℤ) : ℕ := p ^ F.push (j + 1) (F.z j)

/-- **The localiser** `Ξ_loc = Δ_0·∏_{I ∈ mixedCols}(∏_{j<J} Δ_j^{Q_j−1} − ∏_{j<J} minor_{I,j}^{Q_j−1})`. -/
def locPoly : LPol (Fin n') (r + K) R :=
  frameDet F R p K 0 * ∏ I ∈ mixedCols (r := r) (K := K),
    (∏ j ∈ range F.J, frameDet F R p K j ^ (frameQ F p j - 1) -
      ∏ j ∈ range F.J, frameMinor F R p K j I ^ (frameQ F p j - 1))

/-- **Its unscaled part** `Ξ⁰ = ∏_{j<J} Δ_j^{α_j}`, `α_j = [j = 0] + r·K·(Q_j − 1)` (`SymbolData.alpha`). -/
def locLead : LPol (Fin n') (r + K) R := ∏ j ∈ range F.J, frameDet F R p K j ^ F.alpha p (r + K) j

/-- **The budget product** `∏_{j<J} ∏_{x ∈ late j} Tp(j, x)` (one `Tp` per top, the late letters tiling `TT`). -/
def budgetProd : LPol (Fin n') (r + K) R := ∏ j ∈ range F.J, ∏ x ∈ F.late TT j, Tp F TT R p K j x

/-- **The fixed factor** `Ξ⁰^c·budgetProd^{(2Q+3)c}` (the localiser and the iteration budget). -/
def fixFactor (Q c : ℕ) : LPol (Fin n') (r + K) R :=
  locLead F R p K ^ c * budgetProd F TT R p K ^ ((2 * Q + 3) * c)

/-- **The label budget** `labelBudget = budgetProd^{kQ}`. -/
def labelBudget (Q : ℕ) : LPol (Fin n') (r + K) R := budgetProd F TT R p K ^ ((r + K) * Q)

end Explicit

/-! ## Frobenius alignment -/

section Align

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O} {p n' r K : ℕ} [NeZero n']

omit [NeZero n'] in
/-- **Frobenius powers are periodic**: `σ^a = σ^b` when `a ≡ b (mod n′)`. -/
theorem sigma_pow_congr (hU : Unram p n' W Qq O Kf ι σ jW ϖ) {a b : ℕ} (h : a % n' = b % n') : σ ^ a = σ ^ b := by
  rw [← Nat.mod_add_div a n', ← Nat.mod_add_div b n', pow_add, pow_add, pow_mul, pow_mul, hU.period, one_pow,
    one_pow, h]

/-- **The position after `e` steps**: `pos x + e ≡ pos(x + e) (mod n′)`. -/
theorem posOf_add_mod (x : ℤ) (e : ℕ) : ((posOf n' x).val + e) % n' = (posOf n' (x + e)).val % n' := by
  have h1 := posOf_val (n' := n') x
  have h2 := posOf_val (n' := n') (x + e)
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  zify
  rw [h1, h2, Int.emod_emod_of_dvd _ (dvd_refl _), Int.emod_add_emod]

omit [NeZero n'] in
/-- **The Frobenius congruence on twisted entries**: `σ^{a+e}(w) ≡ σ^a(w)^{p^e} (mod p)`, read in `O`. -/
theorem tw_frob (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (a e : ℕ) (w : W) :
    ∃ o : O, ι ((σ ^ (a + e)) (algebraMap W Qq w)) = ι ((σ ^ a) (algebraMap W Qq w)) ^ p ^ e +
      algebraMap O Kf (ϖ ^ 2 * o) := by
  obtain ⟨y, hy⟩ := frob_pow hU e w
  obtain ⟨o, ho⟩ := hU.exists_map_eq a y
  refine ⟨o, ?_⟩
  rw [pow_add]
  show ι ((σ ^ a) ((σ ^ e) (algebraMap W Qq w))) = _
  rw [show algebraMap O Kf (ϖ ^ 2 * o) = (p : Kf) * algebraMap O Kf o by rw [hU.sq, map_mul, map_natCast], ← ho, hy]
  simp only [map_add, map_mul, map_pow, map_natCast]

/-- **Frobenius alignment** (A1): at `g′` over `W` an even row pushed by `p^e` is, modulo `ϖ`, its plane part pushed
by `p^e` times the first `r` rows of `σ^{x + e}(g′⁻¹)`. -/
theorem pent_ad_congr (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n')
    (g' : Matrix (Fin (r + K)) (Fin (r + K)) W) (x : ℤ) (hx : Even x) (e : ℕ) (c : Fin (r + K)) :
    OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (pent Kf p K x e c) -
      ∑ b : Fin r, C (twK ι σ (posOf n' (x + e)).val g'⁻¹ (Fin.castAdd K b) c) *
        pent Kf p K x e (Fin.castAdd K b)) := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  set s := posOf n' x with hsdef
  have hs : vecF n' s = true := by simp [vecF, hsdef, even_posOf_iff hn, hx]
  choose oE hoE using fun (a : ℕ) (w : W) => hU.exists_map_eq a w
  have htw : ∀ a (M : Matrix (Fin (r + K)) (Fin (r + K)) W) i j', twK ι σ a M i j' = algebraMap O Kf (oE a (M i j')) :=
    fun a M i j' => hoE a (M i j')
  set q := p ^ e
  set U : MvPolynomial (Fin n' × Fin (r + K)) O :=
    ∑ b : Fin r, C (oE s.val (g'⁻¹ (Fin.castAdd K b) c)) * X (s, Fin.castAdd K b) with hU'
  set V : MvPolynomial (Fin n' × Fin (r + K)) O :=
    ∑ b : Fin K, C (oE s.val (g'⁻¹ (Fin.natAdd r b) c)) * X (s, Fin.natAdd r b) with hV
  have hlift : ad ι σ ϖ n' r K g' (X (s, c)) = map (algebraMap O Kf) (U + C ϖ * V) := by
    simp only [ad]
    rw [liftSub, aeval_X, Fin.sum_univ_add, map_add, hU', hV, map_sum, map_mul, map_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [scaled, hs, ite_true, Fin.val_castAdd, map_mul, map_C, map_X, htw]
      simp [Nat.not_le.2 b.isLt]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [scaled, hs, ite_true, Fin.val_natAdd, map_mul, map_C, map_X, htw]
      simp only [show r ≤ r + (b : ℕ) by omega, decide_true, ite_true]
      ring
  -- the target as an image
  set o' : Fin r → O := fun b => oE (posOf n' (x + e)).val (g'⁻¹ (Fin.castAdd K b) c)
  have htarget : ∑ b : Fin r, C (twK ι σ (posOf n' (x + e)).val g'⁻¹ (Fin.castAdd K b) c) *
      pent Kf p K x e (Fin.castAdd K b) =
        map (algebraMap O Kf) (∑ b : Fin r, C (o' b) * X (s, Fin.castAdd K b) ^ q) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [pent, map_mul, map_C, map_pow, map_X, htw, o', q, hsdef]
  have hpent : ad ι σ ϖ n' r K g' (pent Kf p K x e c) = map (algebraMap O Kf) ((U + C ϖ * V) ^ q) := by
    rw [pent, map_pow, ← hsdef, hlift, map_pow]
  rw [hpent, htarget, ← map_sub]
  refine TwistedDegree.ordGe_map ?_
  rw [pow_one]
  -- the three congruences
  have h1 : C ϖ ∣ (U + C ϖ * V) ^ q - U ^ q := by
    rw [← geom_sum₂_mul, add_sub_cancel_left]
    exact Dvd.dvd.mul_left (dvd_mul_right (C ϖ) V) _
  obtain ⟨R₀, hR₀⟩ := TwistedDegree.sum_pow_prime_pow hU.prime univ
    (fun b : Fin r => C (oE s.val (g'⁻¹ (Fin.castAdd K b) c)) * X (s, Fin.castAdd K b)) e
  have hpC : (p : MvPolynomial (Fin n' × Fin (r + K)) O) = C ϖ * C ϖ := by
    rw [← map_mul, ← sq, hU.sq, map_natCast]
  have h3 : ∀ b : Fin r, (C ϖ : MvPolynomial (Fin n' × Fin (r + K)) O) ∣
      C (oE s.val (g'⁻¹ (Fin.castAdd K b) c)) ^ q - C (o' b) := by
    intro b
    obtain ⟨o, ho⟩ := tw_frob hU s.val e (g'⁻¹ (Fin.castAdd K b) c)
    have hper : σ ^ (s.val + e) = σ ^ (posOf n' (x + e)).val := sigma_pow_congr hU (posOf_add_mod x e)
    have e1 : oE (posOf n' (x + e)).val (g'⁻¹ (Fin.castAdd K b) c) =
        oE s.val (g'⁻¹ (Fin.castAdd K b) c) ^ q + ϖ ^ 2 * o := by
      apply hinj
      rw [← hoE, ← hper, ho, hoE, map_add, map_pow]
    refine ⟨-C (ϖ * o), ?_⟩
    simp only [o', e1, map_add, map_pow, map_mul]
    ring
  have hsplit : (U + C ϖ * V) ^ q - ∑ b : Fin r, C (o' b) * X (s, Fin.castAdd K b) ^ q =
      ((U + C ϖ * V) ^ q - U ^ q) + (p : MvPolynomial (Fin n' × Fin (r + K)) O) * R₀ +
        ∑ b : Fin r, (C (oE s.val (g'⁻¹ (Fin.castAdd K b) c)) ^ q - C (o' b)) * X (s, Fin.castAdd K b) ^ q := by
    rw [show U ^ q = _ from hR₀]
    simp only [mul_pow, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hpC]
  exact dvd_add (dvd_add h1 (Dvd.intro (C ϖ * R₀) (by ring))) (Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (h3 b) _)

end Align

/-! ## Pushed rows: integrality, supports, the `ϖ`-degree, determinants -/

section Pushed

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O} {p n' r K : ℕ} [NeZero n']

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Pushed entries are integral.** -/
theorem ordGe_pent (x : ℤ) (e : ℕ) (c : Fin (r + K)) : OrdGe ϖ 0 (pent Kf p K x e c : LPol (Fin n') (r + K) Kf) := by
  rw [pent]
  simpa using ordGe_pow (ordGe_X (ϖ := ϖ) (Kf := Kf) (posOf n' x, c)) (p ^ e)

omit [NeZero n'] in
/-- **Twisted entries are integral.** -/
theorem ordGe_C_twK (hU : Unram p n' W Qq O Kf ι σ jW ϖ) {τ : Type*} {k : ℕ} (a : ℕ)
    (M : Matrix (Fin k) (Fin k) W) (i j : Fin k) : OrdGe ϖ 0 (C (twK ι σ a M i j) : MvPolynomial τ Kf) := by
  obtain ⟨o, ho⟩ := hU.exists_map_eq a (M i j)
  rw [twK, Matrix.map_apply, ho]
  exact ordGe_C_int o

/-- **Determinants stay in a subalgebra** containing the entries. -/
theorem det_mem_subalgebra {R' A : Type*} [CommRing R'] [CommRing A] [Algebra R' A] (S : Subalgebra R' A)
    {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix m m A} (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  exact S.sum_mem fun σ' _ => by rw [Units.smul_def]; exact S.zsmul_mem (S.prod_mem fun a _ => h _ _) _

/-- **The weight of the scaled variables**: `1` on a scaled variable, `0` otherwise (`nd` is its weight). -/
def scW (r : ℕ) {n' k : ℕ} : Fin n' × Fin k → ℕ := fun v => if scaled r (vecF n') v then 1 else 0

omit [NeZero n'] in
/-- **`ϖ`-degree conditions are weighted homogeneity** for the weight `scW`. -/
theorem hom_iff {k : ℕ} {R' : Type*} [CommSemiring R'] {P : LPol (Fin n') k R'} {o : ℕ} :
    (∀ m ∈ P.support, nd r (vecF n') m = o) ↔ IsWeightedHomogeneous (scW r) P o :=
  ⟨fun h _ hm => h _ (mem_support_iff.2 hm), fun h _ hm => h (mem_support_iff.1 hm)⟩

/-- **Determinants of homogeneous entries of weight `0`** are homogeneous of weight `0`. -/
theorem isWH_det {τ' R' : Type*} [CommRing R'] {w : τ' → ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m (MvPolynomial τ' R')} (h : ∀ a b, IsWeightedHomogeneous w (M a b) 0) :
    IsWeightedHomogeneous w M.det 0 := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ' _ => ?_
  have hp : IsWeightedHomogeneous w (∏ a, M (σ' a) a) 0 := by
    simpa using IsWeightedHomogeneous.prod univ (fun a => M (σ' a) a) (fun _ => 0) fun a _ => h _ _
  rw [Units.smul_def]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).1
    (zsmul_mem ((mem_weightedHomogeneousSubmodule R' w 0 _).2 hp) _)

omit [NeZero n'] in
/-- **Scaled variables at an even letter**: the normal columns. -/
theorem scaled_even (hn : Even n') {x : ℤ} (hx : Even x) {k : ℕ} (c : Fin k) [NeZero n'] :
    scaled r (vecF n') (posOf n' x, c) = decide (r ≤ c.val) := by
  simp [scaled, vecF, even_posOf_iff hn, hx]

omit [NeZero n'] in
/-- **Scaled variables at an odd letter**: the plane columns. -/
theorem scaled_odd (hn : Even n') {x : ℤ} (hx : ¬ Even x) {k : ℕ} (c : Fin k) [NeZero n'] :
    scaled r (vecF n') (posOf n' x, c) = decide (c.val < r) := by
  simp [scaled, vecF, even_posOf_iff hn, hx]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`Φ_1` on a pushed entry**: the scaling of its variable, raised to the power. -/
theorem ad_one_pent (x : ℤ) (e : ℕ) (c : Fin (r + K)) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (pent Kf p K x e c) =
      C ((if scaled r (vecF n') (posOf n' x, c) then algebraMap O Kf ϖ else 1) ^ p ^ e) * pent Kf p K x e c := by
  rw [pent, map_pow, liftSub_one_X, mul_pow, C_pow]

/-- **An `(r+1) × r` times `r × (r+1)` product has determinant `0`** (pad with a zero column and row). -/
theorem det_mul_eq_zero_of_succ {R' : Type*} [CommRing R'] {m : ℕ} (U : Matrix (Fin (m + 1)) (Fin m) R')
    (M : Matrix (Fin m) (Fin (m + 1)) R') : (Matrix.of fun l c => ∑ b, U l b * M b c).det = 0 := by
  set U' : Matrix (Fin (m + 1)) (Fin (m + 1)) R' := Matrix.of fun l c => Fin.lastCases 0 (U l) c
  set M' : Matrix (Fin (m + 1)) (Fin (m + 1)) R' := Matrix.of fun c l => Fin.lastCases 0 (fun c' => M c' l) c
  have e : (Matrix.of fun l c => ∑ b, U l b * M b c) = U' * M' := by
    ext l l'
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp [U', M']
  rw [e, Matrix.det_mul, Matrix.det_eq_zero_of_column_eq_zero (Fin.last m) fun l => by simp [U'], zero_mul]

/-- **A sum-of-products matrix is a product.** -/
theorem det_of_sum_mul {R' : Type*} [CommRing R'] {m : ℕ} (U M : Matrix (Fin m) (Fin m) R') :
    (Matrix.of fun l c => ∑ b, U l b * M b c).det = U.det * M.det := by
  rw [← Matrix.det_mul]
  congr 1

/-- **Pushed rows with a common target** (`y_l + e_l = x`, even rows): under `Φ_{g′}` their minor on the columns `κ`
is, modulo `ϖ`, the determinant of the plane parts times the first `r` rows of `σ^x(g′⁻¹)` on `κ`. -/
theorem det_ad_pushed (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n')
    (g' : Matrix (Fin (r + K)) (Fin (r + K)) W) {m : ℕ} (y : Fin m → ℤ) (e : Fin m → ℕ) (x : ℤ)
    (hy : ∀ l, Even (y l)) (hye : ∀ l, y l + e l = x) (κ : Fin m → Fin (r + K)) :
    OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (Matrix.of fun l c => pent Kf p K (y l) (e l) (κ c)).det -
      (Matrix.of fun l c => ∑ b : Fin r, pent Kf p K (y l) (e l) (Fin.castAdd K b) *
        C (twK ι σ (posOf n' x).val g'⁻¹ (Fin.castAdd K b) (κ c))).det) := by
  rw [AlgHom.map_det]
  refine ordGe_det_sub (fun a b => ?_) (fun a b => ?_) fun a b => ?_
  · exact ordGe_liftSub hU _ _ _ (ordGe_pent _ _ _)
  · rw [Matrix.of_apply]
    exact ordGe_sum fun b' _ => by simpa using ordGe_mul (ordGe_pent _ _ _) (ordGe_C_twK hU _ _ _ _)
  · have h := pent_ad_congr hU hn g' (y a) (hy a) (e a) (κ b)
    rw [hye a] at h
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    convert h using 2
    exact Finset.sum_congr rfl fun b' _ => mul_comm _ _

variable [NeZero r]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The rows of a late letter** are even tops before it. -/
theorem rows_props {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {j x : ℤ}
    (hx : x ∈ F.late TT j) (l : Fin r) :
    Even (F.rows TT j x l) ∧ F.rows TT j x l < x ∧ IsTop TT (F.rows TT j x l) := by
  have h := F.rows_mem TT (hF.le_card_evBefore (mem_filter.1 hx).2) l
  simp only [FrameSys.evBefore, mem_filter] at h
  exact ⟨h.2.1, h.2.2, (mem_filter.1 h.1).2⟩

end Pushed

/-! ## Keys (N8 C3 at `g = 1`) -/

section Keys

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O} {p n' r K : ℕ} [NeZero n'] [NeZero r]

variable (W ι σ ϖ) in
/-- **A key of level `o`** (main edge): integral, on the tops, `o ≤ 2Q`, with a leading form `κ₀ ∈ ϖ^o O[X]` on the
tops, homogeneous of `ϖ`-degree `o`, `Φ_1 κ ≡ κ₀ (mod ϖ^{o+1})`, and `ord_{g′} κ ≥ o` at **every** `g′ ∈ GL_k(W)`. -/
structure IsPlaneKey (TT : Finset (Fin n')) (Q : ℕ) (κ κ₀ : LPol (Fin n') (r + K) Kf) (o : ℕ) : Prop where
  /-- The key is integral. -/
  int : OrdGe ϖ 0 κ
  /-- The key lives on the tops. -/
  tops : κ ∈ supported Kf {v | v.1 ∈ TT}
  /-- The level is at most `2Q`. -/
  le : o ≤ 2 * Q
  /-- The leading form lives on the tops. -/
  lead_tops : κ₀ ∈ supported Kf {v | v.1 ∈ TT}
  /-- The leading form is homogeneous of `ϖ`-degree `o`. -/
  hom : ∀ m ∈ κ₀.support, nd r (vecF n') m = o
  /-- The leading form has order `o`. -/
  lead : OrdGe ϖ o κ₀
  /-- The leading form is `Φ_1 κ` to order `o + 1`. -/
  err : OrdGe ϖ (o + 1) (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) κ - κ₀)
  /-- The key is small at every `g′ ∈ GL_k(W)`. -/
  small : ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) W, IsUnit g'.det → OrdGe ϖ o (ad ι σ ϖ n' r K g' κ)

omit [IsDomain O] [IsDiscreteValuationRing O] [NeZero r] in
/-- **Pushed entries at a top lie on the tops.** -/
theorem pent_mem_tops {TT : Finset (Fin n')} {x : ℤ} (hx : IsTop TT x) (e : ℕ) (c : Fin (r + K)) :
    pent Kf p K x e c ∈ supported Kf {v : Fin n' × Fin (r + K) | v.1 ∈ TT} := by
  rw [pent]
  exact Subalgebra.pow_mem _ (X_mem_supported.2 (show (posOf n' x, c) ∈ {v : Fin n' × Fin (r + K) | v.1 ∈ TT}
    from hx)) _

omit [NeZero r] in
/-- **Unscaled pushed entries**: a plane column at an even letter has `ϖ`-degree `0`. -/
theorem isWH_pent_plane (hn : Even n') {x : ℤ} (hx : Even x) (e : ℕ) (c : Fin r) :
    IsWeightedHomogeneous (scW r) (pent Kf p K x e (Fin.castAdd K c) : LPol (Fin n') (r + K) Kf) 0 := by
  have h := (isWeightedHomogeneous_X Kf (scW r) (posOf n' x, Fin.castAdd K c)).pow (p ^ e)
  rw [pent]
  simpa [scW, scaled_even hn hx, Nat.not_le.2 c.isLt] using h

/-- **`Tp` is unscaled**: homogeneous of `ϖ`-degree `0`. -/
theorem isWH_Tp (hn : Even n') {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {j x : ℤ}
    (hx : x ∈ F.late TT j) : IsWeightedHomogeneous (scW r) (Tp F TT Kf p K j x) 0 :=
  isWH_det fun l c => isWH_pent_plane hn (rows_props hF hx l).1 _ c

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`Tp` is integral.** -/
theorem ordGe_Tp {TT : Finset (Fin n')} (F : FrameSys n' r) (j x : ℤ) :
    OrdGe ϖ 0 (Tp F TT Kf p K j x) :=
  ordGe_det fun _ _ => ordGe_pent _ _ _

/-- **`Tp` lives on the tops.** -/
theorem Tp_mem_tops {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {j x : ℤ}
    (hx : x ∈ F.late TT j) : Tp F TT Kf p K j x ∈ supported Kf {v : Fin n' × Fin (r + K) | v.1 ∈ TT} :=
  det_mem_subalgebra _ fun l _ => pent_mem_tops (rows_props hF hx l).2.2 _ _

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`Φ_1` fixes `Tp`.** -/
theorem ad_one_Tp (hn : Even n') {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁)
    {j x : ℤ} (hx : x ∈ F.late TT j) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (Tp F TT Kf p K j x) = Tp F TT Kf p K j x := by
  rw [Tp, AlgHom.map_det]
  congr 1
  ext l c
  simp [ad_one_pent, scaled_even hn (rows_props hF hx l).1, Nat.not_le.2 c.isLt]

/-- **A power `p^e ≥ 2`** for `e ≥ 1`. -/
theorem two_le_pow {e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) : 2 ≤ p ^ e :=
  hp.trans (Nat.le_self_pow (by omega) p)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [NeZero n'] [NeZero r] in
/-- **`C ϖ^{q}` has order `2`** for `q ≥ 2`. -/
theorem ordGe_C_pow {τ : Type*} {q : ℕ} (hq : 2 ≤ q) : OrdGe ϖ 2 (C (algebraMap O Kf ϖ ^ q) : MvPolynomial τ Kf) :=
  ordGe_mono hq (by simpa using ordGe_C (τ := τ) (ϖ := ϖ) (Kf := Kf) q 1)

/-- **Even keys** (C3, `x` even): `κ(j, x, b)` is a key of level `1` with leading form `ϖ·X_{x, r+b}·Tp(j, x)`. -/
theorem keyEven_isKey (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) {j x : ℤ} (hx : x ∈ F.late TT j)
    (hxe : Even x) (b : Fin K) :
    IsPlaneKey W ι σ ϖ TT Q (keyEven F TT Kf p K j x b)
      (C (algebraMap O Kf ϖ) * X (posOf n' x, Fin.natAdd r b) * Tp F TT Kf p K j x) 1 := by
  classical
  have hxt : IsTop TT x := (mem_filter.1 (mem_filter.1 hx).1).2
  have hrow := fun l => rows_props hF hx l
  set y : Fin (r + 1) → ℤ := Fin.lastCases x (F.rows TT j x) with hydef
  set e : Fin (r + 1) → ℕ := Fin.lastCases 0 (fun l => (x - F.rows TT j x l).toNat) with hedef
  have hM : keyEven F TT Kf p K j x b = (Matrix.of fun l c => pent Kf p K (y l) (e l) (keyCol b c)).det := by
    rw [keyEven]
    congr 1
    ext l c
    induction l using Fin.lastCases <;> simp [y, e]
  have hy : ∀ l, Even (y l) := fun l => by
    induction l using Fin.lastCases with
    | last => simpa [y] using hxe
    | cast l' => simpa [y] using (hrow l').1
  have hye : ∀ l, y l + e l = x := fun l => by
    induction l using Fin.lastCases with
    | last => simp [y, e]
    | cast l' =>
      simp only [y, e, Fin.lastCases_castSucc]
      rw [Int.toNat_of_nonneg (by linarith [(hrow l').2.1])]
      ring
  have hytop : ∀ l, IsTop TT (y l) := fun l => by
    induction l using Fin.lastCases with
    | last => simpa [y] using hxt
    | cast l' => simpa [y] using (hrow l').2.2
  have hTp := ordGe_Tp (ϖ := ϖ) (TT := TT) F (Kf := Kf) (p := p) (K := K) j x
  refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hM]
    exact ordGe_det fun _ _ => ordGe_pent _ _ _
  · rw [hM]
    exact det_mem_subalgebra _ fun l _ => pent_mem_tops (hytop l) _ _
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (X_mem_supported.2 (show (posOf n' x, Fin.natAdd r b) ∈ {v : Fin n' × Fin (r + K) | v.1 ∈ TT} from hxt)))
      (Tp_mem_tops hF hx)
  · rw [hom_iff]
    have h1 : IsWeightedHomogeneous (scW r) (X (posOf n' x, Fin.natAdd r b) : LPol (Fin n') (r + K) Kf) 1 := by
      simpa [scW, scaled_even hn hxe] using isWeightedHomogeneous_X Kf (scW r) (posOf n' x, Fin.natAdd r b)
    simpa using ((isWeightedHomogeneous_C (scW r) (algebraMap O Kf ϖ)).mul h1).mul (isWH_Tp hn hF hx)
  · simpa using ordGe_mul (ordGe_mul (ordGe_C (τ := Fin n' × Fin (r + K)) (ϖ := ϖ) 1 1) (ordGe_X _)) hTp
  · -- Laplace along the last column
    set A := (ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W)).mapMatrix
      (Matrix.of fun l c => pent Kf p K (y l) (e l) (keyCol b c)) with hA
    rw [hM, AlgHom.map_det, ← hA, Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_castSucc]
    have hlast : (-1 : LPol (Fin n') (r + K) Kf) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) * A (Fin.last r) (Fin.last r) *
        Matrix.det (A.submatrix (Fin.last r).succAbove (Fin.last r).succAbove) =
        C (algebraMap O Kf ϖ) * X (posOf n' x, Fin.natAdd r b) * Tp F TT Kf p K j x := by
      rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Fin.succAbove_last]
      congr 1
      · simp only [hA, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, y, e, keyCol, Fin.lastCases_last]
        rw [ad_one_pent, scaled_even hn hxe]
        simp [pent]
      · rw [Tp]
        congr 1
        ext l c
        simp [hA, y, e, keyCol, ad_one_pent, scaled_even hn (hrow l).1, Nat.not_le.2 c.isLt]
    rw [hlast, add_sub_cancel_right]
    refine ordGe_sum fun l _ => ?_
    have hq : 2 ≤ p ^ e l.castSucc := two_le_pow hp (by
      simp only [e, Fin.lastCases_castSucc]
      have := (hrow l).2.1
      omega)
    have hent : OrdGe ϖ 2 (A l.castSucc (Fin.last r)) := by
      simp only [hA, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, keyCol, Fin.lastCases_last,
        ad_one_pent, scaled_even hn (hy _), Fin.val_natAdd, show r ≤ r + (b : ℕ) by omega, decide_true, ite_true]
      simpa using ordGe_mul (ordGe_C_pow (τ := Fin n' × Fin (r + K)) (Kf := Kf) (ϖ := ϖ) hq) (ordGe_pent _ _ _)
    have hdet : OrdGe ϖ 0 (A.submatrix l.castSucc.succAbove (Fin.last r).succAbove).det :=
      ordGe_det fun _ _ => ordGe_liftSub hU _ _ _ (ordGe_pent _ _ _)
    have hsign : OrdGe ϖ 0 ((-1 : LPol (Fin n') (r + K) Kf) ^ ((l.castSucc : ℕ) + (Fin.last r : ℕ))) := by
      simpa using ordGe_pow (ordGe_neg (ordGe_one (ϖ := ϖ))) (((l.castSucc : Fin (r + 1)) : ℕ) + (Fin.last r : ℕ))
    simpa using ordGe_mul (ordGe_mul hsign hent) hdet
  · intro g' _
    have h := det_ad_pushed hU hn g' y e x hy hye (keyCol b)
    rw [det_mul_eq_zero_of_succ (fun l (b' : Fin r) => pent Kf p K (y l) (e l) (Fin.castAdd K b'))
      (fun b' c => C (twK ι σ (posOf n' x).val g'⁻¹ (Fin.castAdd K b') (keyCol b c))), sub_zero] at h
    rwa [hM]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] [NeZero r] [NeZero n'] in
/-- **`Φ_1` on a variable**, read through `ad`. -/
theorem ad_one_X (v : Fin n' × Fin (r + K)) :
    ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) (X v) =
      C (if scaled r (vecF n') v then algebraMap O Kf ϖ else 1) * X v :=
  liftSub_one_X _ _ _ v

/-- **Odd keys** (C3, `x` odd): `κ(j, x, l)` is a key of level `1` with leading form
`ϖ·Σ_{c<r} X_{x,c}·X_{rows_l, c}^{p^{x − rows_l}}`. -/
theorem keyOdd_isKey (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') (hp : 2 ≤ p) {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) {Q : ℕ} (hQ : 1 ≤ Q) {j x : ℤ} (hx : x ∈ F.late TT j)
    (hxo : ¬ Even x) (l : Fin r) :
    IsPlaneKey W ι σ ϖ TT Q (keyOdd F TT Kf p K j x l)
      (C (algebraMap O Kf ϖ) * ∑ c : Fin r, X (posOf n' x, Fin.castAdd K c) *
        pent Kf p K (F.rows TT j x l) (x - F.rows TT j x l).toNat (Fin.castAdd K c)) 1 := by
  classical
  have hxt : IsTop TT x := (mem_filter.1 (mem_filter.1 hx).1).2
  obtain ⟨hye, hylt, hyt⟩ := rows_props hF hx l
  set yl := F.rows TT j x l with hyl
  set e := (x - yl).toNat with hedef
  have hsum : yl + e = x := by rw [hedef, Int.toNat_of_nonneg (by linarith)]; ring
  have hq : 2 ≤ p ^ e := two_le_pow hp (by omega)
  have hXt : ∀ c : Fin (r + K), (X (posOf n' x, c) : LPol (Fin n') (r + K) Kf) ∈
      supported Kf {v : Fin n' × Fin (r + K) | v.1 ∈ TT} := fun c =>
    X_mem_supported.2 (show (posOf n' x, c) ∈ {v : Fin n' × Fin (r + K) | v.1 ∈ TT} from hxt)
  refine ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · exact ordGe_sum fun c _ => by simpa using ordGe_mul (ordGe_X _) (ordGe_pent _ _ _)
  · exact Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hXt c) (pent_mem_tops hyt _ _)
  · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (hXt _) (pent_mem_tops hyt _ _))
  · rw [hom_iff]
    have hs : IsWeightedHomogeneous (scW r) (∑ c : Fin r, X (posOf n' x, Fin.castAdd K c) *
        pent Kf p K yl e (Fin.castAdd K c) : LPol (Fin n') (r + K) Kf) 1 := by
      refine IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_
      have h1 : IsWeightedHomogeneous (scW r) (X (posOf n' x, Fin.castAdd K c) : LPol (Fin n') (r + K) Kf) 1 := by
        simpa [scW, scaled_odd hn hxo] using isWeightedHomogeneous_X Kf (scW r) (posOf n' x, Fin.castAdd K c)
      simpa using h1.mul (isWH_pent_plane hn hye e c)
    simpa using (isWeightedHomogeneous_C (scW r) (algebraMap O Kf ϖ)).mul hs
  · have hs : OrdGe ϖ 0 (∑ c : Fin r, X (posOf n' x, Fin.castAdd K c) * pent Kf p K yl e (Fin.castAdd K c) :
        LPol (Fin n') (r + K) Kf) := ordGe_sum fun c _ => by simpa using ordGe_mul (ordGe_X _) (ordGe_pent _ _ _)
    simpa using ordGe_mul (ordGe_C (τ := Fin n' × Fin (r + K)) (ϖ := ϖ) 1 1) hs
  · rw [keyOdd, map_sum, Fin.sum_univ_add, mul_sum]
    have hA : ∑ c : Fin r, ad ι σ ϖ n' r K (1 : Matrix (Fin (r + K)) (Fin (r + K)) W)
        (X (posOf n' x, Fin.castAdd K c) * pent Kf p K yl e (Fin.castAdd K c)) =
        ∑ c : Fin r, C (algebraMap O Kf ϖ) * (X (posOf n' x, Fin.castAdd K c) * pent Kf p K yl e (Fin.castAdd K c)) :=
      sum_congr rfl fun c _ => by
        rw [map_mul, ad_one_X, ad_one_pent, scaled_odd hn hxo, scaled_even hn hye]
        simp only [Fin.val_castAdd, c.isLt, decide_true, ite_true, Nat.not_le.2 c.isLt, decide_false,
          Bool.false_eq_true, ite_false, one_pow, map_one, one_mul]
        ring
    rw [hA, add_sub_cancel_left]
    refine ordGe_sum fun b _ => ?_
    rw [map_mul, ad_one_X, ad_one_pent, scaled_odd hn hxo, scaled_even hn hye]
    simp only [Fin.val_natAdd, show ¬ (r + (b : ℕ) < r) by omega, show r ≤ r + (b : ℕ) by omega, decide_true,
      decide_false, Bool.false_eq_true, ite_false, ite_true, map_one, one_mul]
    simpa [mul_comm, mul_assoc, mul_left_comm] using
      ordGe_mul (ordGe_X (ϖ := ϖ) (Kf := Kf) (posOf n' x, Fin.natAdd r b))
        (ordGe_mul (ordGe_C_pow (τ := Fin n' × Fin (r + K)) (Kf := Kf) (ϖ := ϖ) hq) (ordGe_pent yl e (Fin.natAdd r b)))
  · intro g' hg'
    set s := posOf n' x with hsdef
    have happrox : ∀ c, OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (pent Kf p K yl e c) -
        ∑ b : Fin r, C (twK ι σ s.val g'⁻¹ (Fin.castAdd K b) c) * pent Kf p K yl e (Fin.castAdd K b)) := by
      intro c
      have h := pent_ad_congr hU hn g' yl hye e c
      rwa [hsum] at h
    have hXc : ∀ c, ad ι σ ϖ n' r K g' (X (s, c)) =
        ∑ b : Fin (r + K), C ((if (b : ℕ) < r then algebraMap O Kf ϖ else 1) * twK ι σ s.val g' c b) * X (s, b) := by
      intro c
      simp only [ad, liftSub, aeval_X]
      refine sum_congr rfl fun b _ => ?_
      rw [scaled_odd hn hxo]
      simp [vecF, hsdef, even_posOf_iff hn, hxo]
    have hD : OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (keyOdd F TT Kf p K j x l) - ∑ c, ad ι σ ϖ n' r K g' (X (s, c)) *
        ∑ b : Fin r, C (twK ι σ s.val g'⁻¹ (Fin.castAdd K b) c) * pent Kf p K yl e (Fin.castAdd K b)) := by
      rw [keyOdd, map_sum, ← sum_sub_distrib]
      refine ordGe_sum fun c _ => ?_
      rw [map_mul, ← mul_sub]
      simpa using ordGe_mul (ordGe_liftSub hU _ _ g' (ordGe_X (ϖ := ϖ) (Kf := Kf) (s, c))) (happrox c)
    have hS : OrdGe ϖ 1 (∑ c, ad ι σ ϖ n' r K g' (X (s, c)) *
        ∑ b : Fin r, C (twK ι σ s.val g'⁻¹ (Fin.castAdd K b) c) * pent Kf p K yl e (Fin.castAdd K b)) := by
      have e1 : ∀ c, ad ι σ ϖ n' r K g' (X (s, c)) *
          ∑ b : Fin r, C (twK ι σ s.val g'⁻¹ (Fin.castAdd K b) c) * pent Kf p K yl e (Fin.castAdd K b) =
          ∑ b : Fin (r + K), ∑ b' : Fin r, C (twK ι σ s.val g'⁻¹ (Fin.castAdd K b') c * twK ι σ s.val g' c b) *
            (C (if (b : ℕ) < r then algebraMap O Kf ϖ else 1) * X (s, b) * pent Kf p K yl e (Fin.castAdd K b')) := by
        intro c
        rw [hXc, sum_mul]
        refine sum_congr rfl fun b _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun b' _ => ?_
        rw [map_mul, map_mul]
        ring
      rw [sum_congr rfl fun c _ => e1 c, sum_comm]
      refine ordGe_sum fun b _ => ?_
      rw [sum_comm]
      refine ordGe_sum fun b' _ => ?_
      rw [← sum_mul, ← map_sum]
      have hδ : ∑ c, twK ι σ s.val g'⁻¹ (Fin.castAdd K b') c * twK ι σ s.val g' c b =
          if Fin.castAdd K b' = b then 1 else 0 := by
        have := congrFun (congrFun (twK_inv_mul (ι := ι) (σ := σ) s.val hg').1 (Fin.castAdd K b')) b
        rwa [Matrix.mul_apply, Matrix.one_apply] at this
      rw [hδ]
      by_cases hb : Fin.castAdd K b' = b
      · subst hb
        rw [ite_eq_left rfl, ite_eq_left (by simp), map_one, one_mul]
        simpa [mul_assoc] using ordGe_mul (ordGe_C (τ := Fin n' × Fin (r + K)) (ϖ := ϖ) (Kf := Kf) 1 1)
          (ordGe_mul (ordGe_X (ϖ := ϖ) (Kf := Kf) (s, Fin.castAdd K b')) (ordGe_pent yl e (Fin.castAdd K b')))
      · rw [ite_eq_right hb, map_zero, zero_mul]
        exact ordGe_zero 1
    simpa using ordGe_add hD hS

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The odd cofactor identity** (C3): `ϖ·X_{x,c}·Tp(j, x) = Σ_l adj(P)_{c,l}·κ₀(j, x, l)`, `P` the matrix of `Tp`. -/
theorem odd_cofactor_identity {TT : Finset (Fin n')} (F : FrameSys n' r) (j x : ℤ) (c : Fin r) :
    C (algebraMap O Kf ϖ) * X (posOf n' x, Fin.castAdd K c) * Tp F TT Kf p K j x =
      ∑ l : Fin r, (Matrix.of fun l' c' : Fin r => pent Kf p K (F.rows TT j x l')
          (x - F.rows TT j x l').toNat (Fin.castAdd K c')).adjugate c l *
        (C (algebraMap O Kf ϖ) * ∑ c' : Fin r, X (posOf n' x, Fin.castAdd K c') *
          pent Kf p K (F.rows TT j x l) (x - F.rows TT j x l).toNat (Fin.castAdd K c')) := by
  classical
  set P : Matrix (Fin r) (Fin r) (LPol (Fin n') (r + K) Kf) := Matrix.of fun l' c' => pent Kf p K (F.rows TT j x l')
    (x - F.rows TT j x l').toNat (Fin.castAdd K c') with hP
  have h : ∀ c', ∑ l, P.adjugate c l * P l c' = if c = c' then P.det else 0 := fun c' => by
    have := congrFun (congrFun (Matrix.adjugate_mul P) c) c'
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e1 : C (algebraMap O Kf ϖ) * X (posOf n' x, Fin.castAdd K c) * Tp F TT Kf p K j x =
      C (algebraMap O Kf ϖ) * ∑ c', X (posOf n' x, Fin.castAdd K c') * ∑ l, P.adjugate c l * P l c' := by
    simp_rw [h]
    rw [sum_eq_single c (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp only [ite_true, Tp, hP]
    ring
  rw [e1, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun c' _ => ?_
  simp only [hP, Matrix.of_apply]
  ring

end Keys

/-! ## Linear algebra of the localiser: mixed minors, planes, telescoping -/

section LinAlg

/-- **Plane and normal columns differ.** -/
theorem castAdd_ne_natAdd {r K : ℕ} (b : Fin r) (c : Fin K) : Fin.castAdd K b ≠ Fin.natAdd r c := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

/-- **The column map of a mixed set**: the plane columns, with `i′` replaced by the normal column `c`. -/
def mixedFun {r K : ℕ} (i' : Fin r) (c : Fin K) : Fin r → Fin (r + K) :=
  fun l => if l = i' then Fin.natAdd r c else Fin.castAdd K l

/-- **The mixed column sets**: dropping the plane column `i′` and adding the normal column `c`. -/
def mixedSet {r K : ℕ} (i' : Fin r) (c : Fin K) : Finset (Fin (r + K)) := univ.image (mixedFun i' c)

/-- **The column map of a mixed set is injective.** -/
theorem mixedFun_injective {r K : ℕ} (i' : Fin r) (c : Fin K) : Function.Injective (mixedFun i' c) := by
  intro a b hab
  simp only [mixedFun] at hab
  by_cases ha : a = i' <;> by_cases hb : b = i'
  · rw [ha, hb]
  · rw [ite_eq_left ha, ite_eq_right hb] at hab
    exact absurd hab.symm (castAdd_ne_natAdd _ _)
  · rw [ite_eq_right ha, ite_eq_left hb] at hab
    exact absurd hab (castAdd_ne_natAdd _ _)
  · rw [ite_eq_right ha, ite_eq_right hb] at hab
    exact Fin.castAdd_injective _ _ hab

/-- **A mixed set has `r` columns.** -/
theorem card_mixedSet {r K : ℕ} (i' : Fin r) (c : Fin K) : (mixedSet i' c).card = r := by
  rw [mixedSet, card_image_of_injective _ (mixedFun_injective i' c), card_univ, Fintype.card_fin]

/-- **The plane columns of a mixed set**: all but `i′`. -/
theorem mixedSet_filter {r K : ℕ} (i' : Fin r) (c : Fin K) :
    (mixedSet i' c).filter (fun d => d.val < r) = (univ.erase i').image (Fin.castAdd K) := by
  ext d
  simp only [mixedSet, mixedFun, mem_filter, mem_image, mem_univ, true_and, mem_erase, ne_eq, and_true]
  constructor
  · rintro ⟨⟨l, hl⟩, hd⟩
    by_cases hli : l = i'
    · rw [ite_eq_left hli] at hl
      subst hl
      simp at hd
    · rw [ite_eq_right hli] at hl
      exact ⟨l, hli, hl⟩
  · rintro ⟨l, hli, rfl⟩
    exact ⟨⟨l, by rw [ite_eq_right hli]⟩, by simp⟩

/-- **Mixed sets are mixed.** -/
theorem mixedSet_mem {r K : ℕ} [NeZero r] (i' : Fin r) (c : Fin K) : mixedSet i' c ∈ mixedCols (r := r) K := by
  rw [mixedCols, mem_filter]
  refine ⟨mem_univ _, card_mixedSet i' c, ?_⟩
  rw [mixedSet_filter, card_image_of_injective _ (Fin.castAdd_injective _ _), card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_fin]

/-- **Every mixed column set is a `mixedSet`.** -/
theorem exists_mixedSet {r K : ℕ} [NeZero r] {I : Finset (Fin (r + K))} (hI : I ∈ mixedCols (r := r) K) :
    ∃ i' c, I = mixedSet i' c := by
  classical
  rw [mixedCols, mem_filter] at hI
  obtain ⟨-, hc, hp⟩ := hI
  have hr := NeZero.pos r
  have hn : (I.filter fun d => ¬ d.val < r).card = 1 := by
    have := card_filter_add_card_filter_not (s := I) (fun d : Fin (r + K) => d.val < r)
    omega
  obtain ⟨d, hd⟩ := card_eq_one.1 hn
  have hdI : d ∈ I ∧ ¬ d.val < r := mem_filter.1 (hd ▸ mem_singleton_self d)
  set c : Fin K := ⟨d.val - r, by have := d.isLt; omega⟩
  have hdc : d = Fin.natAdd r c := Fin.ext (by simp [c]; omega)
  have hplane : I.filter (fun d => d.val < r) ⊆ univ.image (Fin.castAdd K) := fun e he => by
    have := (mem_filter.1 he).2
    exact mem_image.2 ⟨⟨e.val, this⟩, mem_univ _, Fin.ext rfl⟩
  obtain ⟨i', hi'⟩ : ∃ i' : Fin r, Fin.castAdd K i' ∉ I := by
    by_contra h
    push Not at h
    have : univ.image (Fin.castAdd K) ⊆ I.filter (fun d => d.val < r) := fun e he => by
      obtain ⟨l, -, rfl⟩ := mem_image.1 he
      exact mem_filter.2 ⟨h l, by simp⟩
    have := card_le_card this
    rw [card_image_of_injective _ (Fin.castAdd_injective _ _), card_univ, Fintype.card_fin] at this
    omega
  refine ⟨i', c, (eq_of_subset_of_card_le ?_ (by rw [hc, card_mixedSet])).symm⟩
  have hsub : I.filter (fun d => d.val < r) ⊆ (univ.erase i').image (Fin.castAdd K) := fun e he => by
    obtain ⟨l, -, rfl⟩ := mem_image.1 (hplane he)
    refine mem_image.2 ⟨l, mem_erase.2 ⟨fun h => hi' (h ▸ (mem_filter.1 he).1), mem_univ _⟩, rfl⟩
  have heq : I.filter (fun d => d.val < r) = (univ.erase i').image (Fin.castAdd K) :=
    eq_of_subset_of_card_le hsub (by
      rw [hp, card_image_of_injective _ (Fin.castAdd_injective _ _), card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin])
  intro e he
  obtain ⟨l, -, rfl⟩ := mem_image.1 he
  simp only [mixedFun]
  by_cases hl : l = i'
  · rw [ite_eq_left hl, ← hdc]
    exact hdI.1
  · rw [ite_eq_right hl]
    exact (mem_filter.1 (heq ▸ mem_image.2 ⟨l, mem_erase.2 ⟨hl, mem_univ _⟩, rfl⟩)).1

/-- **`|mixedCols| = r·K`.** -/
theorem card_mixedCols {r K : ℕ} [NeZero r] : (mixedCols (r := r) K).card = r * K := by
  classical
  have e : mixedCols (r := r) K = (univ : Finset (Fin r × Fin K)).image fun x => mixedSet x.1 x.2 := by
    ext I
    simp only [mem_image, mem_univ, true_and, Prod.exists]
    exact ⟨fun h => (exists_mixedSet h).imp fun i' => Exists.imp fun c h => h.symm,
      fun ⟨i', c, h⟩ => h ▸ mixedSet_mem i' c⟩
  rw [e, card_image_of_injective, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rintro ⟨i', c⟩ ⟨i'', c'⟩ h
  simp only at h
  have hc : c = c' := by
    have : Fin.natAdd r c ∈ mixedSet i'' c' := h ▸ mem_image.2 ⟨i', mem_univ _, by simp [mixedFun]⟩
    obtain ⟨l, -, hl⟩ := mem_image.1 this
    simp only [mixedFun] at hl
    split_ifs at hl
    · exact (Fin.natAdd_injective _ _ hl).symm
    · exact absurd hl (castAdd_ne_natAdd _ _)
  subst hc
  refine Prod.ext ?_ rfl
  by_contra hne
  have : Fin.castAdd K i'' ∈ mixedSet i' c := mem_image.2 ⟨i'', mem_univ _, by simp [mixedFun, Ne.symm hne]⟩
  rw [h] at this
  obtain ⟨l, -, hl⟩ := mem_image.1 this
  simp only [mixedFun] at hl
  split_ifs at hl with hli
  · exact castAdd_ne_natAdd _ _ hl.symm
  · exact hli (Fin.castAdd_injective _ _ hl)

/-- **A nonvanishing mixed minor** (C1, the row-reduced matrix): if the plane minor of `N` (`r × (r + K)` over a
field) is invertible and some normal column is nonzero, then the minor on some `I ∈ mixedCols` is nonzero. With
`A = N_{[0,r)}⁻¹·N` and `A_{i′c} ≠ 0`, `I = ([0,r) ∖ {i′}) ∪ {c}`: `A_I` is the identity with column `i′` replaced by
`A_{·c}`, of determinant `A_{i′c}`. -/
theorem exists_mixed_minor {k : Type*} [Field k] {r K : ℕ} [NeZero r] (N : Matrix (Fin r) (Fin (r + K)) k)
    (hP : (N.submatrix id (Fin.castAdd K)).det ≠ 0) {i : Fin r} {c : Fin K} (hc : N i (Fin.natAdd r c) ≠ 0) :
    ∃ I ∈ mixedCols (r := r) K, ∃ h : I.card = r, (N.submatrix id (I.orderEmbOfFin h)).det ≠ 0 := by
  classical
  set P := N.submatrix id (Fin.castAdd K) with hPdef
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  set A := P⁻¹ * N with hAdef
  have hNA : N = P * A := by rw [hAdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
  have hAc : ∀ a l, A a (Fin.castAdd K l) = (1 : Matrix (Fin r) (Fin r) k) a l := by
    intro a l
    have := congrFun (congrFun (Matrix.nonsing_inv_mul P hPu) a) l
    simpa [hAdef, hPdef, Matrix.mul_apply] using this
  obtain ⟨i', hi'⟩ : ∃ i', A i' (Fin.natAdd r c) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    rw [hNA, Matrix.mul_apply]
    simp [h]
  set κ : Fin r → Fin (r + K) := mixedFun i' c with hκdef
  have hκinj : Function.Injective κ := mixedFun_injective i' c
  set I := mixedSet i' c with hIdef
  have hI : I.card = r := card_mixedSet i' c
  have hImix : I ∈ mixedCols (r := r) K := mixedSet_mem i' c
  refine ⟨I, hImix, hI, ?_⟩
  have hmem : ∀ l, κ l ∈ I := fun l => mem_image_of_mem _ (mem_univ _)
  set π : Equiv.Perm (Fin r) := Equiv.ofBijective (fun l => (I.orderIsoOfFin hI).symm ⟨κ l, hmem l⟩)
    (Finite.injective_iff_bijective.1 fun a b hab => hκinj (by
      have := congrArg (fun t => ((I.orderIsoOfFin hI) t : Fin (r + K))) hab
      simpa using this)) with hπ
  have hκ : ∀ l, κ l = I.orderEmbOfFin hI (π l) := fun l => by
    rw [← coe_orderIsoOfFin_apply, hπ, Equiv.ofBijective_apply, OrderIso.apply_symm_apply]
  have hdet : (N.submatrix id κ).det = ((Equiv.Perm.sign π : ℤ) : k) * (N.submatrix id (I.orderEmbOfFin hI)).det := by
    rw [← Matrix.det_permute' π]
    congr 1
    ext a l
    simp [hκ]
  have hκdet : (N.submatrix id κ).det ≠ 0 := by
    have e : N.submatrix id κ = P * A.submatrix id κ := by
      rw [hNA]
      ext a l
      simp [Matrix.mul_apply]
    have e2 : A.submatrix id κ = (1 : Matrix (Fin r) (Fin r) k).updateCol i' (fun a => A a (Fin.natAdd r c)) := by
      ext a l
      by_cases hl : l = i'
      · simp [hκdef, mixedFun, hl]
      · simp [hκdef, mixedFun, hl, hAc]
    have e3 : ((1 : Matrix (Fin r) (Fin r) k).updateCol i' (fun a => A a (Fin.natAdd r c))).det =
        A i' (Fin.natAdd r c) := by
      have := Matrix.det_updateCol_sum (1 : Matrix (Fin r) (Fin r) k) i' (fun a => A a (Fin.natAdd r c))
      simpa [Matrix.one_apply] using this
    rw [e, Matrix.det_mul, e2, e3]
    exact mul_ne_zero hP hi'
  intro h0
  apply hκdet
  rw [hdet, h0, mul_zero]

variable {W : Type} [CommRing W] {r K : ℕ}

/-- **Planes with vanishing normal part** (C1): if the plane minor of the first `r` rows of `g⁻¹` is a unit modulo
`p` and their normal entries vanish modulo `p`, then `g` has the plane of `1`. -/
theorem planeOf_eq_one {p : ℕ} (g : Matrix (Fin (r + K)) (Fin (r + K)) W)
    (hP : IsUnit (Ideal.Quotient.mk (Ideal.span {(p : W)})
      (Matrix.of fun i b : Fin r => g⁻¹ (Fin.castAdd K i) (Fin.castAdd K b)).det))
    (hN : ∀ i c, Ideal.Quotient.mk (Ideal.span {(p : W)}) (g⁻¹ (Fin.castAdd K i) (Fin.natAdd r c)) = 0) :
    planeOf p r g = planeOf p r (1 : Matrix (Fin (r + K)) (Fin (r + K)) W) := by
  classical
  set mk := Ideal.Quotient.mk (Ideal.span {(p : W)}) with hmk
  set Pb : Matrix (Fin r) (Fin r) (W ⧸ Ideal.span {(p : W)}) :=
    Matrix.of fun i b : Fin r => mk (g⁻¹ (Fin.castAdd K i) (Fin.castAdd K b)) with hPb
  have hPbu : IsUnit Pb.det := by
    have e : Pb = mk.mapMatrix (Matrix.of fun i b : Fin r => g⁻¹ (Fin.castAdd K i) (Fin.castAdd K b)) := by
      ext; rfl
    rw [e, ← RingHom.map_det]
    exact hP
  have hinv := Matrix.nonsing_inv_mul Pb hPbu
  have hgen : ∀ (M : Matrix (Fin (r + K)) (Fin (r + K)) W) (i : Fin r),
      (fun c => mk (M⁻¹ (Fin.castAdd K i) c)) ∈ planeOf p r M := fun M i =>
    Submodule.subset_span ⟨Fin.castAdd K i, by simp, rfl⟩
  have hcast : ∀ i : Fin (r + K), (hi : i.val < r) → i = Fin.castAdd K ⟨i.val, hi⟩ := fun i hi => Fin.ext rfl
  apply le_antisymm
  · rw [planeOf, Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    rw [hcast i hi]
    set i' : Fin r := ⟨i.val, hi⟩
    have e : (fun c => mk (g⁻¹ (Fin.castAdd K i') c)) = ∑ b : Fin r, mk (g⁻¹ (Fin.castAdd K i') (Fin.castAdd K b)) •
        (fun c => mk ((1 : Matrix (Fin (r + K)) (Fin (r + K)) W)⁻¹ (Fin.castAdd K b) c)) := by
      ext c
      rw [inv_one, Finset.sum_apply]
      refine Fin.addCases (fun c' => ?_) (fun c' => ?_) c
      · simp [Matrix.one_apply]
      · simp [Matrix.one_apply, hN, castAdd_ne_natAdd]
    rw [e]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hgen 1 b)
  · rw [planeOf, Submodule.span_le]
    rintro v ⟨i, hi, rfl⟩
    rw [hcast i hi]
    set i' : Fin r := ⟨i.val, hi⟩
    have e : (fun c => mk ((1 : Matrix (Fin (r + K)) (Fin (r + K)) W)⁻¹ (Fin.castAdd K i') c)) =
        ∑ m : Fin r, Pb⁻¹ i' m • (fun c => mk (g⁻¹ (Fin.castAdd K m) c)) := by
      ext c
      rw [inv_one, Finset.sum_apply]
      refine Fin.addCases (fun c' => ?_) (fun c' => ?_) c
      · have := congrFun (congrFun hinv i') c'
        simp only [Matrix.mul_apply, hPb, Matrix.of_apply] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [this]
        by_cases h : i' = c'
        · subst h
          simp
        · simp [h]
      · simp [hN, castAdd_ne_natAdd]
    rw [e]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hgen g m)

/-- **Cyclic reindexing**: `∏_{j<J} f(j+1) = ∏_{j<J} f(j)` when `f(J) = f(0)`. -/
theorem prod_range_shift {M : Type*} [CommMonoid M] {J : ℕ} (hJ : 1 ≤ J) (f : ℕ → M) (hf : f J = f 0) :
    ∏ j ∈ range J, f (j + 1) = ∏ j ∈ range J, f j := by
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  rw [prod_range_succ, prod_range_succ' f, hf, mul_comm]

/-- **Telescoping** (C1): if `a(j+1) ≡ a(j)^{Q_j}` modulo an ideal, `a(J) = a(0)`, and `∏ a(j)` is a unit, then
`∏_{j<J} a(j)^{Q_j − 1} ≡ 1`. -/
theorem tele_unit {R : Type*} [CommRing R] (I : Ideal R) {J : ℕ} (hJ : 1 ≤ J) (a : ℕ → R) (Q : ℕ → ℕ)
    (hQ : ∀ j, 1 ≤ Q j) (hstep : ∀ j < J, a (j + 1) - a j ^ Q j ∈ I) (hper : a J = a 0)
    (hu : IsUnit (∏ j ∈ range J, a j)) : ∏ j ∈ range J, a j ^ (Q j - 1) - 1 ∈ I := by
  set q := Ideal.Quotient.mk I
  rw [← Ideal.Quotient.eq]
  have h1 : ∏ j ∈ range J, q (a j) ^ Q j = ∏ j ∈ range J, q (a j) := by
    rw [← prod_range_shift hJ (fun j => q (a j)) (by rw [hper])]
    refine prod_congr rfl fun j hj => ?_
    have := Ideal.Quotient.eq.2 (hstep j (mem_range.1 hj))
    rw [this, map_pow]
  have h2 : q (∏ j ∈ range J, a j ^ (Q j - 1)) * q (∏ j ∈ range J, a j) = q (∏ j ∈ range J, a j) := by
    rw [map_prod, map_prod, ← prod_mul_distrib, ← h1]
    refine prod_congr rfl fun j _ => ?_
    rw [map_pow, ← pow_succ, Nat.sub_add_cancel (hQ j)]
  rw [map_one]
  obtain ⟨u, hu'⟩ := hu.map q
  rw [← hu'] at h2
  calc q (∏ j ∈ range J, a j ^ (Q j - 1)) = q (∏ j ∈ range J, a j ^ (Q j - 1)) * ↑u * ↑u⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = 1 := by rw [h2, Units.mul_inv]

end LinAlg

/-! ## The localiser vanishes off the plane (N8 C1) -/

section Localiser

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {ϖ : O} {p n' r K : ℕ} [NeZero n'] [NeZero r]

/-- **The twisted embedding** `ι ∘ σ^a` of `W` into `Kf`. -/
def tauW (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (a : ℕ) : W →+* Kf := ι.comp ((σ ^ a).toRingHom.comp (algebraMap W Qq))

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The frame rows reach the frame end**: `f(j, l) + push(j, f(j, l)) = z_j`. -/
theorem frame_push {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) (j : ℤ) (l : Fin r) :
    F.f j l + (F.push j (F.f j l) : ℤ) = F.z j := by
  rw [FrameSys.push, Int.toNat_of_nonneg (by linarith [hF.f_le_z j l])]
  ring

/-- **The frame congruence**: modulo `ϖ`, `Φ_{g′}` of the frame `j` on the columns `κ` is `Δ_j` times the twisted
minor of the first `r` rows of `g′⁻¹` on `κ` (Frobenius alignment with target `z_j`). -/
theorem frame_congr (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) (g' : Matrix (Fin (r + K)) (Fin (r + K)) W) (j : ℤ)
    (κ : Fin r → Fin (r + K)) :
    OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (Matrix.of fun l c => pent Kf p K (F.f j l) (F.push j (F.f j l)) (κ c)).det -
      frameDet F Kf p K j * C (tauW ι σ (posOf n' (F.z j)).val
        (Matrix.of fun (b c : Fin r) => g'⁻¹ (Fin.castAdd K b) (κ c)).det)) := by
  have h := det_ad_pushed hU hn g' (F.f j) (fun l : Fin r => F.push j (F.f j l)) (F.z j)
    (fun l => (hF.row_top j l).2) (frame_push hF j) κ
  have e := det_of_sum_mul (Matrix.of fun (l b : Fin r) => (pent Kf p K (F.f j l) (F.push j (F.f j l))
    (Fin.castAdd K b) : LPol (Fin n') (r + K) Kf))
    (Matrix.of fun (b c : Fin r) => (C (twK ι σ (posOf n' (F.z j)).val g'⁻¹ (Fin.castAdd K b) (κ c)) :
      LPol (Fin n') (r + K) Kf))
  simp only [Matrix.of_apply] at e
  rw [e] at h
  convert h using 3
  · rfl
  · change (C.comp (tauW (W := W) ι σ (posOf n' (F.z j)).val)) _ = _
    rw [RingHom.map_det]
    rfl

/-- **Telescoping of the frame Frobenius twists** (C1): for a unit `y ∈ W`,
`∏_{j<J} σ^{z_j}(y)^{Q_j − 1} ≡ 1 (mod p)`, using only Frobenius and `σ^{n′} = 1`. -/
theorem tele_tau (hU : Unram p n' W Qq O Kf ι σ jW ϖ) {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ}
    (hF : F.Proper TT L₁) {y : W} (hy : IsUnit y) :
    ∃ o : O, ∏ j ∈ range F.J, tauW ι σ (posOf n' (F.z j)).val y ^ (frameQ F p j - 1) =
      1 + algebraMap O Kf (ϖ ^ 2 * o) := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  choose oE hoE using fun (a : ℕ) (w : W) => hU.exists_map_eq a w
  set a : ℕ → O := fun j => oE (posOf n' (F.z j)).val y with hadef
  have hτa : ∀ j : ℕ, tauW ι σ (posOf n' (F.z j)).val y = algebraMap O Kf (a j) := fun j => hoE _ _
  have hp1 : 1 ≤ p := hU.prime.one_lt.le
  have hstep : ∀ j < F.J, a (j + 1) - a j ^ frameQ F p j ∈ Ideal.span {ϖ ^ 2} := by
    intro j _
    obtain ⟨o, ho⟩ := tw_frob hU (posOf n' (F.z j)).val (F.push (j + 1) (F.z j)) y
    have hz : F.z j + (F.push (j + 1) (F.z j) : ℤ) = F.z ((j + 1 : ℕ) : ℤ) := by
      have := hF.z_strictMono (show (j : ℤ) < j + 1 by omega)
      rw [FrameSys.push, Int.toNat_of_nonneg (by linarith)]
      push_cast
      ring
    have hper : σ ^ ((posOf n' (F.z j)).val + F.push (j + 1) (F.z j)) = σ ^ (posOf n' (F.z ((j + 1 : ℕ) : ℤ))).val := by
      refine sigma_pow_congr hU ?_
      rw [posOf_add_mod, hz]
    have e : a (j + 1) = a j ^ frameQ F p j + ϖ ^ 2 * o := by
      apply hinj
      rw [hadef]
      simp only
      rw [← hoE, ← hper, ho, hoE, map_add, map_pow, frameQ]
    rw [e, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hper : a F.J = a 0 := by
    simp only [hadef]
    congr 2
    have := hF.z_add_J 0
    rw [zero_add] at this
    rw [Nat.cast_zero, this, show F.z 0 + (n' : ℤ) = F.z 0 + n' * 1 by ring, posOf_add_mul]
  have hu : IsUnit (∏ j ∈ range F.J, a j) := by
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ?_
    obtain ⟨u, rfl⟩ := hy
    refine ⟨⟨a j, oE (posOf n' (F.z j)).val ↑u⁻¹, hinj ?_, hinj ?_⟩, rfl⟩
    · rw [map_mul, map_one, hadef]
      simp only
      rw [← hoE, ← hoE, ← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    · rw [map_mul, map_one, hadef]
      simp only
      rw [← hoE, ← hoE, ← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one]
  have h := tele_unit (Ideal.span {ϖ ^ 2}) hF.one_le_J a (fun j => frameQ F p j)
    (fun j => Nat.one_le_pow _ _ hp1) hstep hper hu
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.1 h
  refine ⟨o, ?_⟩
  simp_rw [hτa]
  rw [show ∏ x ∈ range F.J, algebraMap O Kf (a x) ^ (frameQ F p x - 1) =
      algebraMap O Kf (∏ x ∈ range F.J, a x ^ (frameQ F p x - 1)) by simp [map_prod, map_pow],
    show ∏ x ∈ range F.J, a x ^ (frameQ F p x - 1) = 1 + ϖ ^ 2 * o by linear_combination -ho, map_add, map_one]

/-- **The localiser vanishes off the plane** (C1): `ord_{g′} Ξ_loc ≥ 1` for `g′` off the main plane. With `N` the first
`r` rows of `g′⁻¹`, each frame minor is `≡ Δ_j·σ^{z_j}(det N_I)`; if `det N_{[0,r)} ≡ 0` the factor `Δ_0` vanishes,
otherwise some `I ∈ mixedCols` has `det N_I` a unit (`exists_mixed_minor`, `planeOf_eq_one`), and by telescoping both
products in the `I`-th factor are `≡ ∏_j Δ_j^{Q_j−1}`. -/
theorem locPoly_offPlane (hU : Unram p n' W Qq O Kf ι σ jW ϖ) (hn : Even n') {TT : Finset (Fin n')}
    {F : FrameSys n' r} {L₁ : ℕ} (hF : F.Proper TT L₁) (g' : Matrix (Fin (r + K)) (Fin (r + K)) W)
    (hg' : OffPlane p g') :
    OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (locPoly F Kf p K)) := by
  classical
  obtain ⟨-, hpl⟩ := hg'
  set mk := Ideal.Quotient.mk (Ideal.span {(p : W)}) with hmk
  have hmax : (Ideal.span {(p : W)}).IsMaximal := by
    rw [← hU.unif_W.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal W
  have hunit : ∀ w : W, mk w ≠ 0 → IsUnit w := fun w hw => by
    rw [hmk, Ne, Ideal.Quotient.eq_zero_iff_mem, ← hU.unif_W.maximalIdeal_eq] at hw
    exact IsLocalRing.notMem_maximalIdeal.1 hw
  set dK : (Fin r → Fin (r + K)) → W := fun κ => (Matrix.of fun (b c : Fin r) => g'⁻¹ (Fin.castAdd K b) (κ c)).det
    with hdK
  set τ : ℤ → W →+* Kf := fun j => tauW ι σ (posOf n' (F.z j)).val with hτdef
  set Q : ℕ → ℕ := fun j => frameQ F p j - 1 with hQ
  have hΔ : ∀ j, OrdGe ϖ 0 (frameDet F Kf p K j) := fun j => ordGe_det fun _ _ => ordGe_pent _ _ _
  have hM : ∀ j I, OrdGe ϖ 0 (frameMinor F Kf p K j I) := fun j I => by
    rw [frameMinor]
    split_ifs
    exacts [ordGe_det fun _ _ => ordGe_pent _ _ _, ordGe_zero 0]
  have hadΔ : ∀ j, OrdGe ϖ 0 (ad ι σ ϖ n' r K g' (frameDet F Kf p K j)) := fun j => ordGe_liftSub hU _ _ _ (hΔ j)
  have hadM : ∀ j I, OrdGe ϖ 0 (ad ι σ ϖ n' r K g' (frameMinor F Kf p K j I)) := fun j I =>
    ordGe_liftSub hU _ _ _ (hM j I)
  have hτ : ∀ j w, OrdGe ϖ 0 (C (τ j w) : LPol (Fin n') (r + K) Kf) := fun j w => by
    obtain ⟨o, ho⟩ := hU.exists_map_eq (posOf n' (F.z j)).val w
    exact ordGe_C_iff.2 ⟨o, by rw [pow_zero, one_mul, ← ho]; rfl⟩
  have hcD : ∀ j, OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (frameDet F Kf p K j) -
      frameDet F Kf p K j * C (τ j (dK (Fin.castAdd K)))) := fun j => frame_congr hU hn hF g' j (Fin.castAdd K)
  have hcM : ∀ j I (h : I.card = r), OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (frameMinor F Kf p K j I) -
      frameDet F Kf p K j * C (τ j (dK (I.orderEmbOfFin h)))) := fun j I h => by
    rw [frameMinor, dite_eq_left h]
    exact frame_congr hU hn hF g' j _
  have hfac : ∀ I, OrdGe ϖ 0 (∏ j ∈ range F.J, ad ι σ ϖ n' r K g' (frameDet F Kf p K j) ^ Q j -
      ∏ j ∈ range F.J, ad ι σ ϖ n' r K g' (frameMinor F Kf p K j I) ^ Q j) := fun I =>
    ordGe_sub (ordGe_prod fun j _ => by simpa using ordGe_pow (hadΔ j) (Q j))
      (ordGe_prod fun j _ => by simpa using ordGe_pow (hadM j I) (Q j))
  rw [locPoly, map_mul, map_prod]
  simp only [map_sub, map_prod, map_pow]
  by_cases hdP : mk (dK (Fin.castAdd K)) = 0
  · -- the plane minor vanishes modulo `p`: the factor `Δ_0`
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdP)
    have hC : OrdGe ϖ 1 (C (τ 0 (dK (Fin.castAdd K))) : LPol (Fin n') (r + K) Kf) := by
      obtain ⟨o, ho⟩ := hU.exists_map_eq (posOf n' (F.z 0)).val w
      refine ordGe_mono (by norm_num : 1 ≤ 2) (ordGe_C_iff.2 ⟨o, ?_⟩)
      rw [← hw, map_mul, map_natCast, LocalLattice.castK_eq_sq hU, map_mul, map_pow]
      rw [show τ 0 w = algebraMap O Kf o from ho]
      ring
    have h0 : OrdGe ϖ 1 (ad ι σ ϖ n' r K g' (frameDet F Kf p K 0)) := by
      have := ordGe_add (hcD 0) (by simpa using ordGe_mul (hΔ 0) hC)
      simpa using this
    simpa using ordGe_mul h0 (ordGe_prod fun I _ => hfac I)
  · -- the plane minor is a unit: some mixed minor is a unit
    have hdPu : IsUnit (dK (Fin.castAdd K)) := hunit _ hdP
    let _ : Field (W ⧸ Ideal.span {(p : W)}) := Ideal.Quotient.field _
    have hmkdP : mk (dK (Fin.castAdd K)) =
        (Matrix.of fun i b : Fin r => mk (g'⁻¹ (Fin.castAdd K i) (Fin.castAdd K b))).det := by
      rw [hdK, RingHom.map_det]
      rfl
    obtain ⟨i, c, hic⟩ : ∃ i c, mk (g'⁻¹ (Fin.castAdd K i) (Fin.natAdd r c)) ≠ 0 := by
      by_contra h
      push Not at h
      exact hpl (planeOf_eq_one g' (isUnit_iff_ne_zero.2 hdP) h)
    set Nb : Matrix (Fin r) (Fin (r + K)) (W ⧸ Ideal.span {(p : W)}) :=
      Matrix.of fun b c => mk (g'⁻¹ (Fin.castAdd K b) c) with hNb
    obtain ⟨I₀, hI₀, h₀, hdet₀⟩ := exists_mixed_minor Nb (by rw [hmkdP] at hdP; exact hdP) hic
    have hdIu : IsUnit (dK (I₀.orderEmbOfFin h₀)) := hunit _ (by
      rw [hdK, RingHom.map_det]
      exact hdet₀)
    obtain ⟨o₁, ho₁⟩ := tele_tau (ϖ := ϖ) hU hF hdPu
    obtain ⟨o₂, ho₂⟩ := tele_tau (ϖ := ϖ) hU hF hdIu
    set ΔP := ∏ j ∈ range F.J, frameDet F Kf p K j ^ Q j with hΔP
    have hΔPi : OrdGe ϖ 0 ΔP := ordGe_prod fun j _ => by simpa using ordGe_pow (hΔ j) (Q j)
    have hsplit : ∀ y : W, ∏ j ∈ range F.J, (frameDet F Kf p K j * C (τ j y)) ^ Q j =
        ΔP * C (∏ j ∈ range F.J, τ j y ^ Q j) := fun y => by
      rw [hΔP, map_prod, ← prod_mul_distrib]
      exact prod_congr rfl fun j _ => by rw [mul_pow, map_pow]
    have hA : OrdGe ϖ 1 (∏ j ∈ range F.J, ad ι σ ϖ n' r K g' (frameDet F Kf p K j) ^ Q j -
        ΔP * C (∏ j ∈ range F.J, τ j (dK (Fin.castAdd K)) ^ Q j)) := by
      rw [← hsplit]
      exact ordGe_prod_sub_prod (fun j _ => by simpa using ordGe_pow (hadΔ j) (Q j))
        (fun j _ => by simpa using ordGe_pow (ordGe_mul (hΔ j) (hτ j _)) (Q j))
        (fun j _ => ordGe_pow_sub_pow (hadΔ j) (by simpa using ordGe_mul (hΔ j) (hτ j _)) (hcD j) _)
    have hB : OrdGe ϖ 1 (∏ j ∈ range F.J, ad ι σ ϖ n' r K g' (frameMinor F Kf p K j I₀) ^ Q j -
        ΔP * C (∏ j ∈ range F.J, τ j (dK (I₀.orderEmbOfFin h₀)) ^ Q j)) := by
      rw [← hsplit]
      exact ordGe_prod_sub_prod (fun j _ => by simpa using ordGe_pow (hadM j I₀) (Q j))
        (fun j _ => by simpa using ordGe_pow (ordGe_mul (hΔ j) (hτ j _)) (Q j))
        (fun j _ => ordGe_pow_sub_pow (hadM j I₀) (by simpa using ordGe_mul (hΔ j) (hτ j _)) (hcM j I₀ h₀) _)
    have hdiff : OrdGe ϖ 1 (ΔP * C (∏ j ∈ range F.J, τ j (dK (Fin.castAdd K)) ^ Q j) -
        ΔP * C (∏ j ∈ range F.J, τ j (dK (I₀.orderEmbOfFin h₀)) ^ Q j)) := by
      rw [← mul_sub, ← map_sub]
      have e1 : ∏ j ∈ range F.J, τ j (dK (Fin.castAdd K)) ^ Q j -
          ∏ j ∈ range F.J, τ j (dK (I₀.orderEmbOfFin h₀)) ^ Q j = algebraMap O Kf (ϖ ^ 2 * (o₁ - o₂)) := by
        simp only [hτdef, hQ]
        rw [ho₁, ho₂, add_sub_add_left_eq_sub, ← map_sub, mul_sub]
      rw [e1]
      simpa using ordGe_mul hΔPi (ordGe_mono (by norm_num : 1 ≤ 2) (ordGe_C (τ := Fin n' × Fin (r + K)) 2 (o₁ - o₂)))
    have hfac0 : OrdGe ϖ 1 (∏ j ∈ range F.J, ad ι σ ϖ n' r K g' (frameDet F Kf p K j) ^ Q j -
        ∏ j ∈ range F.J, ad ι σ ϖ n' r K g' (frameMinor F Kf p K j I₀) ^ Q j) := by
      have := ordGe_add (ordGe_sub hA hB) hdiff
      convert this using 1
      ring
    rw [← mul_prod_erase _ _ hI₀]
    simpa using ordGe_mul (hadΔ 0) (ordGe_mul hfac0 (ordGe_prod fun I _ => hfac I))

end Localiser

/-! ## The localiser at the plane; integrality (N8 C2 at `g = 1`) -/

section AtPlane

/-- **The scaled ideal**: the polynomials all of whose monomials have `ϖ`-degree `≥ 1` (the ideal generated by the
scaled variables). -/
def scIdeal (r : ℕ) {n' k : ℕ} (R : Type*) [CommRing R] : Ideal (LPol (Fin n') k R) where
  carrier := {P | ∀ m ∈ P.support, 1 ≤ nd r (vecF n') m}
  add_mem' {a b} ha hb m hm := (Finset.mem_union.1 (support_add hm)).elim (ha m) (hb m)
  zero_mem' := by simp
  smul_mem' c P hP m hm := by
    classical
    obtain ⟨a, -, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul c P hm)
    rw [map_add]
    exact le_add_left (hP b hb)

/-- **Scaled variables lie in the scaled ideal.** -/
theorem X_mem_scIdeal {r n' k : ℕ} {R : Type*} [CommRing R] {v : Fin n' × Fin k} (hv : scaled r (vecF n') v) :
    (X v : LPol (Fin n') k R) ∈ scIdeal r R := by
  classical
  intro m hm
  rw [mem_support_iff, coeff_X] at hm
  split_ifs at hm with h
  · rw [← h]
    simp [nd, Finsupp.weight_single, hv]
  · exact absurd rfl hm

/-- **A determinant with a column in an ideal** lies in the ideal. -/
theorem det_mem_of_col {R' : Type*} [CommRing R'] (I : Ideal R') {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m R'} (c₀ : m) (h : ∀ a, M a c₀ ∈ I) : M.det ∈ I := by
  rw [Matrix.det_apply]
  refine I.sum_mem fun σ' _ => ?_
  rw [Units.smul_def, ← Finset.mul_prod_erase _ _ (mem_univ c₀)]
  exact zsmul_mem (I.mul_mem_right _ (h _)) _

variable {n' r : ℕ} [NeZero n'] [NeZero r] {p K : ℕ} {TT : Finset (Fin n')} {F : FrameSys n' r} {L₁ : ℕ}

/-- **Frame minors on mixed columns are scaled**: the normal column of `I` sits at even rows. -/
theorem frameMinor_mem_scIdeal {R : Type*} [CommRing R] (hn : Even n') (hp : 1 ≤ p) (hF : F.Proper TT L₁) (j : ℤ)
    {I : Finset (Fin (r + K))} (hI : I ∈ mixedCols (r := r) K) : frameMinor F R p K j I ∈ scIdeal r R := by
  have hI' := (mem_filter.1 hI).2
  obtain ⟨d, hdI, hd⟩ : ∃ d ∈ I, ¬ d.val < r := by
    by_contra h
    push Not at h
    have := filter_true_of_mem h
    rw [this, hI'.1] at hI'
    have := NeZero.pos r
    omega
  rw [frameMinor, dite_eq_left hI'.1]
  obtain ⟨t₀, ht₀⟩ : d ∈ Set.range (I.orderEmbOfFin hI'.1) := by rw [range_orderEmbOfFin]; exact hdI
  refine det_mem_of_col _ t₀ fun l => ?_
  simp only [Matrix.of_apply, ht₀, pent]
  refine Ideal.pow_mem_of_mem _ (X_mem_scIdeal ?_) _ (pow_pos (by omega) _)
  rw [scaled_even hn (hF.row_top j l).2]
  simpa using hd

/-- **`Δ_j` is unscaled.** -/
theorem isWH_frameDet {R : Type*} [CommRing R] (hn : Even n') (hF : F.Proper TT L₁) (j : ℤ) :
    IsWeightedHomogeneous (scW r) (frameDet F R p K j) 0 :=
  isWH_det fun l c => by
    have h := (isWeightedHomogeneous_X R (scW r) (posOf n' (F.f j l), Fin.castAdd K c)).pow (p ^ F.push j (F.f j l))
    simp only [Matrix.of_apply, pent]
    simpa [scW, scaled_even hn (hF.row_top j l).2, Nat.not_le.2 c.isLt] using h

/-- **`Ξ⁰` is unscaled.** -/
theorem isWH_locLead {R : Type*} [CommRing R] (hn : Even n') (hF : F.Proper TT L₁) :
    IsWeightedHomogeneous (scW r) (locLead F R p K) 0 := by
  have h := IsWeightedHomogeneous.prod (range F.J) (fun j : ℕ => frameDet F R p K j ^ F.alpha p (r + K) j)
    (fun _ => 0) fun j _ => by simpa using (isWH_frameDet (R := R) (K := K) (p := p) hn hF j).pow (F.alpha p (r + K) j)
  simpa [locLead] using h

/-- **`Ξ⁰ = Δ_0·(∏_j Δ_j^{Q_j−1})^{rK}`.** -/
theorem locLead_eq {R : Type*} [CommRing R] (hF : F.Proper TT L₁) :
    locLead F R p K = frameDet F R p K 0 *
      (∏ j ∈ range F.J, frameDet F R p K j ^ (frameQ F p j - 1)) ^ (mixedCols (r := r) K).card := by
  rw [card_mixedCols, locLead]
  have e : ∀ j ∈ range F.J, frameDet F R p K j ^ F.alpha p (r + K) j =
      frameDet F R p K j ^ (if (j : ℤ) = 0 then 1 else 0) * (frameDet F R p K j ^ (frameQ F p j - 1)) ^ (r * K) :=
    fun j _ => by
      rw [FrameSys.alpha, pow_add, ← pow_mul, show r + K - r = K by omega, frameQ]
      congr 2
      ring
  rw [prod_congr rfl e, prod_mul_distrib, prod_pow]
  congr 1
  rw [prod_eq_single 0 (fun j _ hj => by simp [hj]) (fun h => absurd (mem_range.2 hF.one_le_J) h)]
  simp

/-- **The localiser at the plane** (C2 at `g = 1`): `Ξ⁰` is unscaled and every monomial of `Ξ_loc − Ξ⁰` is scaled
(`|mixedCols| = rK`, and every mixed minor has a normal column at even rows, `Q_0 − 1 ≥ 1`). -/
theorem locPoly_sub_locLead {Kf : Type} [Field Kf] (hn : Even n') (hp : 2 ≤ p) (hF : F.Proper TT L₁) :
    (∀ m ∈ (locLead F Kf p K).support, nd r (vecF n') m = 0) ∧
      ∀ m ∈ (locPoly F Kf p K - locLead F Kf p K).support, 1 ≤ nd r (vecF n') m := by
  classical
  refine ⟨hom_iff.2 (isWH_locLead hn hF), ?_⟩
  change locPoly F Kf p K - locLead F Kf p K ∈ scIdeal r Kf
  rw [← Ideal.Quotient.eq, locPoly, locLead_eq hF, map_mul, map_mul, map_prod, map_pow]
  congr 1
  have hQ0 : 1 ≤ frameQ F p ((0 : ℕ) : ℤ) - 1 := by
    have h1 : 1 ≤ F.push ((0 : ℕ) + 1) (F.z (0 : ℕ)) := by
      have := hF.z_strictMono (show ((0 : ℕ) : ℤ) < (0 : ℕ) + 1 by omega)
      rw [FrameSys.push]
      omega
    have : p ≤ frameQ F p ((0 : ℕ) : ℤ) := by rw [frameQ]; exact Nat.le_self_pow (by omega) p
    omega
  have hMI : ∀ I ∈ mixedCols (r := r) K,
      ∏ j ∈ range F.J, frameMinor F Kf p K j I ^ (frameQ F p j - 1) ∈ scIdeal r Kf := by
    intro I hI
    rw [← mul_prod_erase _ _ (mem_range.2 hF.one_le_J)]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (frameMinor_mem_scIdeal hn (by omega) hF _ hI) _
      (by omega))
  rw [← prod_const]
  refine prod_congr rfl fun I hI => ?_
  rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 (hMI I hI), sub_zero]

/-- **Integrality and support** of the explicit polynomials (`ℤ`-coefficients, letters on the tops). -/
theorem explicit_int {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {ϖ : O} (hn : Even n')
    (hF : F.Proper TT L₁) :
    OrdGe ϖ 0 (locPoly F Kf p K) ∧ locPoly F Kf p K ∈ supported Kf {v | v.1 ∈ TT} ∧
      Unscaled ϖ TT (budgetProd F TT Kf p K) ∧ Unscaled ϖ TT (locLead F Kf p K) := by
  classical
  have hΔ : ∀ j, OrdGe ϖ 0 (frameDet F Kf p K j) := fun j => ordGe_det fun _ _ => ordGe_pent _ _ _
  have hM : ∀ j I, OrdGe ϖ 0 (frameMinor F Kf p K j I) := fun j I => by
    rw [frameMinor]
    split_ifs
    exacts [ordGe_det fun _ _ => ordGe_pent _ _ _, ordGe_zero 0]
  have hΔs : ∀ j, frameDet F Kf p K j ∈ supported Kf {v : Fin n' × Fin (r + K) | v.1 ∈ TT} := fun j =>
    det_mem_subalgebra _ fun l _ => pent_mem_tops (hF.row_top j l).1 _ _
  have hMs : ∀ j I, frameMinor F Kf p K j I ∈ supported Kf {v : Fin n' × Fin (r + K) | v.1 ∈ TT} := fun j I => by
    rw [frameMinor]
    split_ifs
    exacts [det_mem_subalgebra _ fun l _ => pent_mem_tops (hF.row_top j l).1 _ _, Subalgebra.zero_mem _]
  have hLi : OrdGe ϖ 0 (locLead F Kf p K) := ordGe_prod fun j _ => by simpa using ordGe_pow (hΔ j) _
  have hLs : locLead F Kf p K ∈ supported Kf {v : Fin n' × Fin (r + K) | v.1 ∈ TT} :=
    Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (hΔs j) _
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ⟨hLi, hLs, hom_iff.2 (isWH_locLead hn hF)⟩⟩
  · exact ordGe_mul (hΔ 0) (ordGe_prod fun I _ => ordGe_sub (ordGe_prod fun j _ => by
      simpa using ordGe_pow (hΔ j) _) (ordGe_prod fun j _ => by simpa using ordGe_pow (hM j I) _))
  · exact Subalgebra.mul_mem _ (hΔs 0) (Subalgebra.prod_mem _ fun I _ => Subalgebra.sub_mem _
      (Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (hΔs j) _)
      (Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (hMs j I) _))
  · exact ordGe_prod fun j _ => ordGe_prod fun x _ => ordGe_Tp F j x
  · exact Subalgebra.prod_mem _ fun j _ => Subalgebra.prod_mem _ fun x hx => Tp_mem_tops hF hx
  · refine hom_iff.2 ?_
    have h := IsWeightedHomogeneous.prod (range F.J) (fun j : ℕ => ∏ x ∈ F.late TT j, Tp F TT Kf p K j x)
      (fun _ => 0) fun j _ => by
        simpa using IsWeightedHomogeneous.prod (F.late TT j) (fun x => Tp F TT Kf p K j x) (fun _ => 0)
          fun x hx => isWH_Tp hn hF hx
    simpa [budgetProd] using h

end AtPlane

end

end SourceKeys
