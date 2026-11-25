import Mathlib
import ThetaChain

/-!
# The local volumes of the theta kernels (spec-3 §1)

The local factor `Ξ_j` of a step `j < m − 1` is `∏_{P ∈ S} volN_P(j)⁻¹ · E1(om(Φ_P))`, and the `E1 ∘ om ∘ Φ` part has a
fixed scale; so the volumes `volN_P(j)` carry the scale of `Ξ_j`. This module defines them, the factor itself
(`E1`, `om`, `PhiG`, `PhiQ`, `XiStd`; spec-2 1d) and the pins `XiFull` (`Ξ_j = XiStd`) and `XiScale` (`Ξ_j(0)` is
`XiStd(0)` up to a unit of absolute value `1` at every complex place). The frontier (L7) uses `XiScale`: the
orientation (the library's `x` is the transpose of the archive's), the `FC` clause `s − n′ = c` (vacuous as
written), the triangularity sense of `PhiG` and the sharp shape `PhiGS` are not certain [I]. `XiVolPinned` (the
root-of-unity form) is not used by the frontier.

All groups are subgroups of `GL_{n+c}(E)` for the global field `E`; `P`-local integrality enters through lattices of
`E^{n+c}` defined by valuations at `P` (`intAt`; `stdAt P = sclLat P 0` is the localised standard lattice). Following
`ThetaChain`, a subgroup cut out by conditions that are closed under products and inverses is written as a
`Subgroup.closure` (the closure adds nothing).

* `R1 n c`: the matrices `[[A, B], [0, U]]` with `U` upper unitriangular and column `n` equal to `e_n`; `fixX`
  (`A = I`); `N1 = R1 ⊓ fixX`.
* `stabL M`, `sclLat`, `scE`, `lamY`, `parL`, `JQ`; `flagU`, `flagG`, `bvecG`, `JG`.
* `Cbe J h = R1 ⊓ hJh⁻¹`, `volN C N₀ = [C ∩ N1 : C ∩ N₀] / [N₀ : C ∩ N₀]` (Mathlib's `relIndex`), `volAt`.

**Parameters.** The index shuffle `fIdx`/`fPos` of `JG` (spec-3 describes it only as moving the `c` extra
coordinates to positions `k₀, …, k₀ + c − 1`) is a pair of functions `ℕ → ℕ`. The group at the places `SG` enters
`XiVolPinned` as a parameter `JS` (`JG` for the unsharp kernel, the untranscribed `JGsym` for the sharp one), and so
do the double-coset representatives `h` (to be taken from the `ChIdx` bundle of the levels, spec-3 §1 caveat).
So are the kernel shapes `Φ_P` (`PhiG ∘ entB` unsharp, the untranscribed `PhiGS` sharp, `PhiQ ∘ entB` at `Q`), the
additive characters `ψ_P`, the local characters `μ_P` and `sq_P = √q`, with their stated properties (`LocOk`); `E1`
uses the depth `A = B` (a parameter; the archive's `E1` is stable for large `A`, `B`).
-/

namespace ThetaVol

open NumberField IsDedekindDomain ThetaChain

section Groups

variable {E : Type*} [Field E] [NumberField E] (n c : ℕ)

/-- The block shape of `R1` (spec-3 §1): zero below the diagonal in the rows `≥ n`, ones on the diagonal there, and
column `n` equal to `e_n`. -/
def IsR1 (M : Matrix (Fin (n + c)) (Fin (n + c)) E) : Prop :=
  ∀ a b : Fin (n + c), (n ≤ (a : ℕ) → (b : ℕ) < a → M a b = 0) ∧ (n ≤ (a : ℕ) → a = b → M a b = 1) ∧
    ((a : ℕ) < n → (b : ℕ) = n → M a b = 0)

/-- `R1`: the `r = [[A, B], [0, U]]` with `U` upper unitriangular and `r e_n = e_n`, a mirabolic-type group. -/
def R1 : Subgroup (GL (Fin (n + c)) E) :=
  Subgroup.closure {g | IsR1 n c g.1 ∧ IsR1 n c g⁻¹.1}

/-- `fixX`: `r e_l = e_l` for `l < n` (the block `A` is the identity). -/
def fixX : Subgroup (GL (Fin (n + c)) E) :=
  Subgroup.closure {g | ∀ a b : Fin (n + c), (b : ℕ) < n → g.1 a b = if a = b then 1 else 0}

/-- `N1 = R1 ∩ fixX`: the `[[I, B], [0, U]]`. -/
def N1 : Subgroup (GL (Fin (n + c)) E) := R1 n c ⊓ fixX n c

variable {n c}

/-- The stabiliser `{g : g x ∈ M ↔ x ∈ M}` of a lattice `M`. -/
def stabL (M : Set (Fin (n + c) → E)) : Subgroup (GL (Fin (n + c)) E) :=
  Subgroup.closure {g | ∀ x, g.1.mulVec x ∈ M ↔ x ∈ M}

/-- `x ∈ O_(P)`. -/
def intAt (Pl : HeightOneSpectrum (𝓞 E)) (x : E) : Prop := Pl.valuation E x ≤ 1

/-- `q_P = N(P)`, as in `ThetaChain.locLat`. -/
noncomputable def qP (Pl : HeightOneSpectrum (𝓞 E)) : E := ((Ideal.absNorm Pl.asIdeal : ℕ) : E)

/-- The scaled lattice `sclLat(e) = {v : q^{−e(l)} v_l ∈ O_(P) for all l}`. -/
def sclLat (Pl : HeightOneSpectrum (𝓞 E)) (e : ℕ → ℤ) : Set (Fin (n + c) → E) :=
  {v | ∀ l : Fin (n + c), intAt Pl (qP Pl ^ (-e l) * v l)}

/-- `scE(n, ex)(l) = 0` for `l < n`, `ex(l − n)` otherwise. -/
def scE (n : ℕ) (ex : ℕ → ℤ) (l : ℕ) : ℤ := if l < n then 0 else ex (l - n)

variable (n c) in
/-- `lamY(n, c, ex) = sclLat(scE n ex)`; with `ex = (i ↦ i + 1)` the lattice scaled by `q^{i+1}` on the `i`-th extra
coordinate. -/
def lamY (Pl : HeightOneSpectrum (𝓞 E)) (ex : ℕ → ℤ) : Set (Fin (n + c) → E) := sclLat Pl (scE n ex)

variable (n c) in
/-- `J` at a place of `Q`: `JQ(kj, n, c) = stabL(stdAt) ∩ stabL(parL)`, `parL = sclLat(l ↦ [kj ≤ l < n])`. -/
def JQ (Pl : HeightOneSpectrum (𝓞 E)) (kj : ℕ) : Subgroup (GL (Fin (n + c)) E) :=
  stabL (sclLat Pl 0) ⊓ stabL (sclLat Pl fun l => if kj ≤ l ∧ l < n then 1 else 0)

/-- The basis vector `e_l` (`0` if `l ≥ n + c`). -/
def eN (l : ℕ) : Fin (n + c) → E := fun a => if (a : ℕ) = l then 1 else 0

/-- `flagU(M, e, r, st)`: stabilise `M s` for `s ∈ st`, and for `s < r` stabilise `M s` with `κ(e s) − e s ∈ M s`. -/
def flagU (M : ℕ → Set (Fin (n + c) → E)) (e : ℕ → Fin (n + c) → E) (r : ℕ) (st : Set ℕ) :
    Subgroup (GL (Fin (n + c)) E) :=
  Subgroup.closure {κ | (∀ s ∈ st, κ ∈ stabL (M s)) ∧ ∀ s < r, κ ∈ stabL (M s) ∧ κ.1.mulVec (e s) - e s ∈ M s}

variable (n c) in
/-- `flagG(s) = sclLat(l ↦ scE n (i ↦ i + 1) l + [s ≤ fPos l])`; the shuffle `fPos` is a parameter. -/
def flagG (Pl : HeightOneSpectrum (𝓞 E)) (fPos : ℕ → ℕ) (s : ℕ) : Set (Fin (n + c) → E) :=
  sclLat Pl fun l => scE n (fun i => i + 1) l + if s ≤ fPos l then 1 else 0

variable (n c) in
/-- `bvecG(s) = q^{scE(fIdx s)} e_{fIdx s}`; the shuffle `fIdx` is a parameter. -/
noncomputable def bvecG (Pl : HeightOneSpectrum (𝓞 E)) (fIdx : ℕ → ℕ) (s : ℕ) : Fin (n + c) → E :=
  qP Pl ^ scE n (fun i => i + 1) (fIdx s) • eN (fIdx s)

variable (n c) in
/-- `J` at a place of `SG` (unsharp): `JG = stabL(lamY(i ↦ i + 1)) ∩ flagU(flagG, bvecG, r, {r + i·t})`, for a given
index shuffle `fIdx`/`fPos`. Meant for L7, as a value of `XiVolPinned`'s parameter `JS`. -/
noncomputable def JG (Pl : HeightOneSpectrum (𝓞 E)) (fIdx fPos : ℕ → ℕ) (r t : ℕ) : Subgroup (GL (Fin (n + c)) E) :=
  stabL (lamY n c Pl fun i => i + 1) ⊓ flagU (flagG n c Pl fPos) (bvecG n c Pl fIdx) r {s | ∃ i, s = r + i * t}

variable (n c) in
/-- `Cbe(J, h) = R1 ∩ hJh⁻¹ = {g ∈ R1 : h⁻¹gh ∈ J}`. -/
def Cbe (J : Subgroup (GL (Fin (n + c)) E)) (h : GL (Fin (n + c)) E) : Subgroup (GL (Fin (n + c)) E) :=
  R1 n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

variable (n c) in
/-- `volN(C, N₀) = [C ∩ N1 : C ∩ N₀] / [N₀ : C ∩ N₀]` (Mathlib's `H.relIndex K = [K : H ⊓ K]`, and `N₀ ≤ N1`). -/
noncomputable def volN (C N₀ : Subgroup (GL (Fin (n + c)) E)) : ℚ :=
  (N₀.relIndex (C ⊓ N1 n c) : ℚ) / (C.relIndex N₀ : ℚ)

omit [NumberField E] in
/-- **The volume is positive** when both indices are finite. -/
theorem volN_pos (C N₀ : Subgroup (GL (Fin (n + c)) E)) (h₁ : N₀.relIndex (C ⊓ N1 n c) ≠ 0)
    (h₂ : C.relIndex N₀ ≠ 0) : 0 < volN n c C N₀ :=
  div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₁)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₂))

open Classical in
variable (n c) in
/-- The local volume `volN_P` of a step at `P`: `J = JS` at `P ∈ SG`, `JQ(kj)` at `P ∈ Q`;
`N₀ = N1 ∩ stabL(lamY(ex))` with `ex = (i ↦ i + 1)` at `SG`, `ex = 0` at `Q`. -/
noncomputable def volAt (SG : Finset (HeightOneSpectrum (𝓞 E))) (JS : Subgroup (GL (Fin (n + c)) E)) (kj : ℕ)
    (h : GL (Fin (n + c)) E) (Pl : HeightOneSpectrum (𝓞 E)) : ℚ :=
  volN n c (Cbe n c (if Pl ∈ SG then JS else JQ n c Pl kj) h)
    (N1 n c ⊓ stabL (lamY n c Pl (if Pl ∈ SG then fun i => i + 1 else 0)))

end Groups

section Kernel

variable {E L : Type*} [Field E] [NumberField E] [Field L]

/-- `v(a) = ord_P a` (`0` at `a = 0`). -/
noncomputable def vP (Pl : HeightOneSpectrum (𝓞 E)) (a : E) : ℤ := -WithZero.log (Pl.valuation E a)

/-- `a ∈ P·O_(P)`. -/
def inP (Pl : HeightOneSpectrum (𝓞 E)) (a : E) : Prop := Pl.valuation E a < 1

/-- The local character `μ = locChar(muq, χ)`: `μ(a) = muq^{v(a)}·χ(a/q^{v(a)})`, where `χ` stands for `χ ∘ red` on
the `P`-units. -/
noncomputable def locChar (Pl : HeightOneSpectrum (𝓞 E)) (muq : L) (χ : E → L) (a : E) : L :=
  muq ^ vP Pl a * χ (a / qP Pl ^ vP Pl a)

/-- Entry `(l, s)` of `y` in the archive's orientation (rows `l` the source), i.e. the library's entry `(s, l)`; `0`
out of range. The library's matrices act on columns (`homAt`), the archive's on rows [I]. -/
def entA {a b : ℕ} (y : Matrix (Fin b) (Fin a) E) (l s : ℕ) : E :=
  if h : s < b ∧ l < a then y ⟨s, h.1⟩ ⟨l, h.2⟩ else 0

/-- The free positions `FC` of `E1`, as library positions `(s, l)`: archive column `s ≥ n′`, and `s − n′ = c` or
`l < n` or `l − n < s − n′` (spec-2 1d, verbatim). -/
abbrev FC (n n' c c' : ℕ) :=
  {p : Fin (n' + c') × Fin (n + c) // n' ≤ (p.1 : ℕ) ∧ ((p.1 : ℕ) - n' = c ∨ (p.2 : ℕ) < n ∨ (p.2 : ℕ) - n < p.1 - n')}

/-- `x̃(x, t)`: `x` in the top-left block, `t` at the free positions `FC`, `1` at archive `(n + s − n′, s)`, `0`
elsewhere. -/
def xTil (n n' c c' : ℕ) (x : Matrix (Fin n') (Fin n) E) (t : FC n n' c c' → E) :
    Matrix (Fin (n' + c')) (Fin (n + c)) E :=
  fun s l => if h : (s : ℕ) < n' ∧ (l : ℕ) < n then x ⟨s, h.1⟩ ⟨l, h.2⟩
    else if h' : n' ≤ (s : ℕ) ∧ ((s : ℕ) - n' = c ∨ (l : ℕ) < n ∨ (l : ℕ) - n < s - n') then t ⟨(s, l), h'⟩
    else if n' ≤ (s : ℕ) ∧ (l : ℕ) = n + (s - n') then 1 else 0

/-- `E1(Φ)(x) = q^{−A·|FC|}·Σ_t Φ(x̃(x, t))·ψ(−Σ_{i<c} x̃_{n+i, n′+i+1})`, `t` over `valsQ^{FC}`, `valsQ =
{i/q^A : 0 ≤ i < q^{2A}}` (representatives of `q^{−A}O_P/q^A O_P`; the spec's `A = B`). -/
noncomputable def E1 (q A n n' c c' : ℕ) (ψ : E → L) (Φ : Matrix (Fin (n' + c')) (Fin (n + c)) E → L)
    (x : Matrix (Fin n') (Fin n) E) : L :=
  ((q : L) ^ (A * Fintype.card (FC n n' c c')))⁻¹ * ∑ t : FC n n' c c' → Fin (q ^ (2 * A)),
    Φ (xTil n n' c c' x fun p => ((t p : ℕ) : E) / (q : E) ^ A) *
      ψ (-∑ i : Fin c, entA (xTil n n' c c' x fun p => ((t p : ℕ) : E) / (q : E) ^ A) (n + i) (n' + i + 1))

/-- The level twist `om(Φ)(x) = μ(det g)·μ(det h)⁻¹·sq^{−v(det g)·b}·sq^{v(det h)·a}·Φ(h⁻¹xg)`, `g ∈ GL_a`,
`h ∈ GL_b` the representatives, `sq = √q`. -/
noncomputable def om (Pl : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (μ : E → L) (sq : L) (g : GL (Fin a) E)
    (h : GL (Fin b) E) (Φ : Matrix (Fin b) (Fin a) E → L) (x : Matrix (Fin b) (Fin a) E) : L :=
  μ (g : Matrix (Fin a) (Fin a) E).det * (μ (h : Matrix (Fin b) (Fin b) E).det)⁻¹ *
    sq ^ (-(vP Pl (g : Matrix (Fin a) (Fin a) E).det * b)) * sq ^ (vP Pl (h : Matrix (Fin b) (Fin b) E).det * a) *
    Φ (((h⁻¹ : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) * x * (g : Matrix (Fin a) (Fin a) E))

/-- `entB(y)`: `y` in the archive orientation with rows and columns shuffled by `fR`, `fC` (the `fIdx` shuffle,
a parameter) and entry `(p, p′)` scaled by `q^{exC(p′) − exR(p)}`. -/
noncomputable def entB {a b : ℕ} (Pl : HeightOneSpectrum (𝓞 E)) (fR fC : ℕ → ℕ) (exR exC : ℕ → ℤ)
    (y : Matrix (Fin b) (Fin a) E) (p p' : ℕ) : E :=
  qP Pl ^ (exC p' - exR p) * entA y (fR p) (fC p')

/-- The `k × k` determinant of `M` on the indices `o, …, o + k − 1`. -/
noncomputable def blkDet (M : ℕ → ℕ → E) (o k : ℕ) : E := (Matrix.of fun p p' : Fin k => M (o + p) (o + p')).det

open Classical in
/-- The kernel shape at `P ∈ SG` (unsharp; `M = entB(x)`, `a = r + i·t`): `0` unless (i) the first `a` columns
are integral, their rows `≥ a` in `P`; (ii) `M_{p′p′} ≡ 1` for `p′ < r` and `M_{pp′} ≡ 0` for `p′ < p < a`,
`p′ < r`; (iii) the `t × t` blocks beyond `r` are block triangular in the same sense; then
`ψ₀(Σ_{p<r−1} M_{p,p+1})·∏_{l<i} χ_l(det block_l)·χ_i(det M_{<a,<a})⁻¹`, with `ψ₀(red y) = ψ(y/q)`. -/
noncomputable def PhiG (Pl : HeightOneSpectrum (𝓞 E)) (ψ : E → L) (χ : ℕ → E → L) (r t i : ℕ)
    (M : ℕ → ℕ → E) : L :=
  if (∀ p p', p' < r + i * t → intAt Pl (M p p') ∧ (r + i * t ≤ p → inP Pl (M p p'))) ∧
      (∀ p' < r, inP Pl (M p' p' - 1)) ∧ (∀ p p', p' < p → p < r + i * t → p' < r → inP Pl (M p p')) ∧
      (∀ p p', r ≤ p' → p < r + i * t → (p' - r) / t < (p - r) / t → inP Pl (M p p'))
  then ψ ((∑ p ∈ Finset.range (r - 1), M p (p + 1)) / qP Pl) *
    (∏ l ∈ Finset.range i, χ l (blkDet M (r + l * t) t)) * (χ i (blkDet M 0 (r + i * t)))⁻¹
  else 0

open Classical in
/-- The kernel shape at `P ∈ Q` (`M = entB(x)`): `ξ_P(red det M_{<r,<r})` if `M` is integral, its rows `≥ r` in
the first `r` columns lie in `P` and the determinant is a unit; else `0`. -/
noncomputable def PhiQ (Pl : HeightOneSpectrum (𝓞 E)) (ξ : E → L) (r : ℕ) (M : ℕ → ℕ → E) : L :=
  if (∀ p p', intAt Pl (M p p')) ∧ (∀ p p', r ≤ p → p' < r → inP Pl (M p p')) ∧ ¬ inP Pl (blkDet M 0 r)
  then ξ (blkDet M 0 r) else 0

/-- **The local factor** `Ξ(x) = ∏_{P ∈ R} volN_P⁻¹·E1(om(Φ_P))(x)` of a step from size `n + c` to `n′ + c′`, `R` the
row set, `g`, `h` the representatives, `Φ_P` the kernel shapes (`PhiG ∘ entB` or the untranscribed sharp `PhiGS` at
`SG`, `PhiQ ∘ entB` at `Q`: a parameter, as `JS`). -/
noncomputable def XiStd (n n' c c' A : ℕ) (R SG : Finset (HeightOneSpectrum (𝓞 E)))
    (JS : HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (n' + c')) E)) (kj : ℕ)
    (g : HeightOneSpectrum (𝓞 E) → GL (Fin (n + c)) E) (h : HeightOneSpectrum (𝓞 E) → GL (Fin (n' + c')) E)
    (ψ μ : HeightOneSpectrum (𝓞 E) → E → L) (sq : HeightOneSpectrum (𝓞 E) → L)
    (Ph : HeightOneSpectrum (𝓞 E) → Matrix (Fin (n' + c')) (Fin (n + c)) E → L) (x : Matrix (Fin n') (Fin n) E) : L :=
  ∏ Pl ∈ R, (((volAt n' c' SG (JS Pl) kj (h Pl) Pl)⁻¹ : ℚ) : L) *
    E1 (Ideal.absNorm Pl.asIdeal) A n n' c c' (ψ Pl) (om Pl (μ Pl) (sq Pl) (g Pl) (h Pl) (Ph Pl)) x

/-- The local parameters' stated properties (spec-2 1d) at the places `R`: `sq² = q`; `ψ` additive, trivial on
`O_(P)`, with `ψ(a/q) = ψ₀(red a)` through `σ₀`; `μ = locChar(muq, χ)`; `Φ_P` valued in the roots of unity and `0`.
Meant for L7. -/
def LocOk (σ₀ : L →+* ℂ) (xi0 : E) (R : Finset (HeightOneSpectrum (𝓞 E))) (ψ μ : HeightOneSpectrum (𝓞 E) → E → L)
    (sq : HeightOneSpectrum (𝓞 E) → L) {a b : ℕ} (Ph : HeightOneSpectrum (𝓞 E) → Matrix (Fin b) (Fin a) E → L) :
    Prop :=
  ∀ Pl ∈ R, sq Pl ^ 2 = (Ideal.absNorm Pl.asIdeal : L) ∧ (∀ y z, ψ Pl (y + z) = ψ Pl y * ψ Pl z) ∧
    (∀ y, intAt Pl y → ψ Pl y = 1) ∧
    (∀ y : 𝓞 E, σ₀ (ψ Pl ((y : E) / qP Pl)) = psi0 xi0 Pl (Ideal.Quotient.mk Pl.asIdeal y)) ∧
    (∃ muq χ, μ Pl = locChar Pl muq χ) ∧ ∀ y, Ph Pl y = 0 ∨ ∃ r, 0 < r ∧ Ph Pl y ^ r = 1

end Kernel

section Pin

variable {E L : Type*} [Field E] [NumberField E] [IsCMField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {τ : Φ → (E →+* L)}

/-- **The scale of `Ξ_j` is pinned** (spec-3 §1): for `j < m − 1`, `Ξ_j(c, c′)` at the trivial coset is
`(∏_{P ∈ S} volN_P(j))⁻¹` times a root of unity, the volumes taken at size `N_{j+1} + (m − 2 − j)` with the
representatives `h_{j+1, c′}`, `J = JS` at `SG` and `JQ(k + j + 1)` at `Q = S \ SG`. `h` and `JS` are parameters
(the `ChIdx` representatives; `JG` or the sharp `JGsym`). Meant for L7. -/
def XiVolPinned (D : Data τ) (m k : ℕ) (h : ∀ j, D.β j → D.S → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E)) : Prop :=
  ∀ j, j + 1 < m → ∀ c c', ∃ ζ : L, (∃ r, 0 < r ∧ ζ ^ r = 1) ∧
    D.Xi j c c' 0 = (((∏ᶠ Pl : D.S, volAt (D.n (j + 1)) (m - 1 - (j + 1)) D.SG (JS (j + 1) Pl)
      (k + (j + 1)) (h (j + 1) c'.1 Pl) Pl : ℚ)⁻¹ : ℚ) : L) * ζ

/-- `XiStd` at step `j < m − 1` of `D`: sizes `N_j + c_j → N_{j+1} + c_{j+1}` (`c_j = m − 1 − j`), representatives
`g = h_{j,c}`, `h = h_{j+1,c′}`, `J = JS` at `SG` and `JQ(k + j + 1)` at `Q = R \ SG`; local parameters per step. -/
noncomputable def xiStd (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L)
    (j : ℕ) (c : Cls D.n D.ST D.SG D.β D.Λ j) (c' : Cls D.n D.ST D.SG D.β D.Λ (j + 1)) :
    Matrix (Fin (D.n (j + 1))) (Fin (D.n j)) E → L :=
  XiStd (D.n j) (D.n (j + 1)) (m - 1 - j) (m - 1 - (j + 1)) A R D.SG (JS (j + 1)) (k + (j + 1)) (h j c.1)
    (h (j + 1) c'.1) (ψ j) (μ j) (sq j) (Ph j)

/-- **The local factors are pinned** (spec-3 §1): `Ξ_j = XiStd` for `j < m − 1`, with the representatives `h` (the
`ChIdx` bundle's), the groups `JS` and the local parameters passed in. The full form; the frontier uses `XiScale`. -/
def XiFull (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L) : Prop :=
  ∀ j, j + 1 < m → ∀ c c', D.Xi j c c' = xiStd D m A k R h JS ψ μ sq Ph j c c'

/-- **The scale of `Ξ_j` is pinned** (spec-3 §1, verdict): for `j < m − 1`, `Ξ_j(c, c′)` at the trivial coset is
`XiStd` there up to a unit `u` with `|u| = 1` at every complex place (harmless for slopes by the product formula).
Meant for L7 (`IsThetaCol`, untwisted level). -/
def XiScale (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L) : Prop :=
  ∀ j, j + 1 < m → ∀ c c', ∃ u : L, (∀ σ : L →+* ℂ, ‖σ u‖ = 1) ∧
    D.Xi j c c' 0 = xiStd D m A k R h JS ψ μ sq Ph j c c' 0 * u

/-- **Sanity:** the full pin gives the scale pin (`u = 1`). -/
theorem XiFull.scale {D : Data τ} {m A k : ℕ} {R : Finset (HeightOneSpectrum (𝓞 E))}
    {h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E}
    {JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E)}
    {ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L} {sq : ℕ → HeightOneSpectrum (𝓞 E) → L}
    {Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L}
    (hX : XiFull D m A k R h JS ψ μ sq Ph) : XiScale D m A k R h JS ψ μ sq Ph :=
  fun j hj c c' => ⟨1, fun σ => by simp, by rw [hX j hj c c', mul_one]⟩

end Pin

end ThetaVol
