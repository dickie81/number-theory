import Mathlib
import ThetaChain

/-!
# The local volumes of the theta kernels (spec-3 §1)

The local factor `Ξ_j` of a generic step `j < m − 2` is `∏_{P ∈ S} volN_P(j)⁻¹ · E1(om(Φ_P))`, and the `E1 ∘ om ∘ Φ`
part has a fixed scale; so the volumes `volN_P(j)` carry the scale of `Ξ_j`. This module defines them, the factor itself
(`E1`, `om`, `PhiGS`, `PhiQ`, `XiStd`; spec-2 1d as corrected by spec-6) and the pins `XiFull`
(`Ξ_j = XiStd`) and `XiScale` (`Ξ_j(0)` is `XiStd(0)` up to a unit of absolute value `1` at every complex place). The
two top steps differ (spec-10 F1–F5; the archive's `XiCpl1`, `XiCpl2`, coupled through the coset `Y` of level `m − 1`,
here in its collapsed form `ȳ ∈ ∏_{P ∈ Q} (O/P^{m−1})^{N_{m−1}}`): step `m − 2` is `xiCpl` (`XiStd` at `SG`;
`q^{−(m−1)N_{m−1}}·om(Φ_P)([x | ȳ_P])` at `Q`, `joinCol`, no `E1`, no `volN`) and step `m − 1` is `xiTop` (`PhiTop·ftY`,
read on the row point's lift). All three read `x` at each place `P` in the frames of the source and the target
(`HermClasses.inFr`, `ThetaChain.DecoF.frAt`: the archive's `inFr` with `frsF`, the frame lifts `liftFr` at `SG` and the
lattice frames at `Q`), and carry the level-`T` indicator
`HermClasses.phiT` (the top's target is the lift `tilQ`, whose `f_P = tz·a` it reads). The frontier (L7) uses `XiFull`
with the canonical sharp instance (`jS`, `phS`, `LocOk`, depth `m + 1`). The library's `x` is the archive's (no
transpose); `entB` uses the archive's shuffle `fIdx` with `k₀ = k`. The unsharp kernel shape and group at `SG` and the
root-of-unity form of the scale pin are not part of the frontier and are not defined.

All groups are subgroups of `GL_{n+c}(E)` for the global field `E`; `P`-local integrality enters through lattices of
`E^{n+c}` defined by valuations at `P` (`intAt`; `stdAt P = sclLat P 0` is the localised standard lattice). Following
`ThetaChain`, a subgroup cut out by conditions that are closed under products and inverses is written as a
`Subgroup.closure` (the closure adds nothing).

* `R1 n c`: the matrices `[[A, B], [0, U]]` with `U` upper unitriangular and column `n` equal to `e_n`; `fixX`
  (`A = I`); `N1 = R1 ⊓ fixX`.
* `stabL M`, `sclLat`, `scE`, `lamY`, `parL`, `JQ`; `flagU`, `bvecG` (the sharp `flagS`, `bvecS`, `JGsym` below).
* `Cbe J h = R1 ⊓ hJh⁻¹`, `volN C N₀ = [C ∩ N1 : C ∩ N₀] / [N₀ : C ∩ N₀]` (Mathlib's `relIndex`), `volAt`.
* `TwNF`: the archive's normal form of the representatives at `P ∈ Q` (spec-12 F6).
* `blkA`, `n1Arg`, `prX`, `LevQOk`: the level group `prX(Cbe(JQ, h)) ∩ GL_n(O_(P))` of the classes at `P ∈ Q` and
  its character `chiInv` (the archive's `grpQ`, `chrQ`, with the `ψ_P(n1Arg)` factor; spec-12 F6), which L7 ties to
  `ChIdx.levQ`, `ChIdx.chrQ`; `IsRed`, `LevGOk`: the level group `red_w(prX(R1 ∩ J))` at `w ∈ SG` (the archive's
  `grpG`), tied to `ChIdx.Λ`; `lamGS`: the value of `PhiGS` before its last factor, which gives the level character at
  `SG` (the archive's `lamGvS`, `chrG`), tied to `ChIdx.chr`; `SameDC`: the double cosets `R1·h·J` (the archive's
  `inj`, `IdxProd`, `surj`).
* `XiStdAt`: the factor of `XiStd` at one place (read alone at `Q` by L7's `surj`).

**Parameters.** `bvecG` takes the index shuffle as a parameter; `entB` and `JGsym` use the archive's `fIdx`/`fPos`
(spec-6 §6). `XiStd` takes the group `JS` at `SG`, the representatives `h` (the `ChIdx` bundle's, spec-3 §1 caveat),
the kernel shapes `Φ_P`, the additive characters `ψ_P`, the local characters `μ_P` and `sq_P = √q` as parameters;
`LocOk` pins the canonical ones (spec-6 §4, spec-7 §3), `jS`/`phS` are the canonical sharp `JS`/`Φ_P` at `SG`, and
`phQ` the canonical `Φ_P` at `Q`. The row set is `SG ∪ Q` (spec-7 §3a; `Q = ∅` at the untwisted level). `E1` uses
the depth `A = B` (a parameter; the canonical one is `m + 1`).
-/

namespace ThetaVol

open NumberField IsDedekindDomain ThetaChain HermClasses

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

/-- `q_P = N(P)`. -/
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
/-- `bvecG(s) = q^{scE(fIdx s)} e_{fIdx s}`; the shuffle `fIdx` is a parameter. -/
noncomputable def bvecG (Pl : HeightOneSpectrum (𝓞 E)) (fIdx : ℕ → ℕ) (s : ℕ) : Fin (n + c) → E :=
  qP Pl ^ scE n (fun i => i + 1) (fIdx s) • eN (fIdx s)

variable (n c) in
/-- `Cbe(J, h) = R1 ∩ hJh⁻¹ = {g ∈ R1 : h⁻¹gh ∈ J}`. -/
def Cbe (J : Subgroup (GL (Fin (n + c)) E)) (h : GL (Fin (n + c)) E) : Subgroup (GL (Fin (n + c)) E) :=
  R1 n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

variable (n c) in
/-- `h′ ∈ R1·h·J` (the archive's `SameDC`): `h` and `h′` lie in one double coset `R1 \ GL_{n+c}(E) / J`. Distinct
indices of a level have representatives in distinct double cosets at some place of `Q`, with `J = JQ(k + j)` (the
archive's `inj`), indices in one double coset have one representative (`IdxProd`), and every tuple of double cosets
reached place by place by nonzero step factors at `Q` is some index's (`surj`; `SharpChain.IsThetaCol`). -/
def SameDC (J : Subgroup (GL (Fin (n + c)) E)) (h h' : GL (Fin (n + c)) E) : Prop :=
  ∃ r ∈ R1 n c, ∃ κ ∈ J, h' = r * h * κ

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

/-- Entry `(l, s)` (row `l`, the target; column `s`, the source) of `y`, `0` out of range. The library's `x` is the
archive's `x` (spec-6 §0–1: both act on columns, rows the target), so there is no transpose. -/
def entA {a b : ℕ} (y : Matrix (Fin b) (Fin a) E) (l s : ℕ) : E :=
  if h : l < b ∧ s < a then y ⟨l, h.1⟩ ⟨s, h.2⟩ else 0

/-- The free positions `FC` of `E1` (spec-6 §2), as pairs `(row, col)`: `n ≤ col` and either `col − n = c′` (the
last source extra coordinate; `c = c′ + 1`) or `1 ≤ col − n` and (`row < n′` or `row − n′ < col − n`). -/
abbrev FC (n n' c c' : ℕ) :=
  {p : Fin (n' + c') × Fin (n + c) // n ≤ (p.2 : ℕ) ∧
    ((p.2 : ℕ) - n = c' ∨ (1 ≤ (p.2 : ℕ) - n ∧ ((p.1 : ℕ) < n' ∨ (p.1 : ℕ) - n' < p.2 - n)))}

/-- `x̃(x, t)` (rows `l`, columns `s`): `x` in the top-left block, `t` at the free positions `FC`, `1` at
`(n′ + (s − n), s)` for `s ≥ n`, `0` elsewhere (spec-6 §2). -/
def xTil (n n' c c' : ℕ) (x : Matrix (Fin n') (Fin n) E) (t : FC n n' c c' → E) :
    Matrix (Fin (n' + c')) (Fin (n + c)) E :=
  fun l s => if h : (l : ℕ) < n' ∧ (s : ℕ) < n then x ⟨l, h.1⟩ ⟨s, h.2⟩
    else if h' : n ≤ (s : ℕ) ∧ ((s : ℕ) - n = c' ∨ (1 ≤ (s : ℕ) - n ∧ ((l : ℕ) < n' ∨ (l : ℕ) - n' < s - n)))
      then t ⟨(l, s), h'⟩
    else if n ≤ (s : ℕ) ∧ (l : ℕ) = n' + (s - n) then 1 else 0

/-- `E1(Φ)(x) = q^{−A·|FC|}·Σ_t Φ(x̃(x, t))·ψ(−Σ_{i<c′} x̃_{n′+i, n+i+1})`, `t` over `valsQ^{FC}`, `valsQ =
{i/q^A : 0 ≤ i < q^{2A}}` (representatives of `q^{−A}O_P/q^A O_P`; the archive's `A = B`; spec-6 §1). -/
noncomputable def E1 (q A n n' c c' : ℕ) (ψ : E → L) (Φ : Matrix (Fin (n' + c')) (Fin (n + c)) E → L)
    (x : Matrix (Fin n') (Fin n) E) : L :=
  ((q : L) ^ (A * Fintype.card (FC n n' c c')))⁻¹ * ∑ t : FC n n' c c' → Fin (q ^ (2 * A)),
    Φ (xTil n n' c c' x fun p => ((t p : ℕ) : E) / (q : E) ^ A) *
      ψ (-∑ i : Fin c', entA (xTil n n' c c' x fun p => ((t p : ℕ) : E) / (q : E) ^ A) (n' + i) (n + i + 1))

/-- The level twist `om(Φ)(x) = μ(det g)·μ(det h)⁻¹·sq^{−v(det g)·b}·sq^{v(det h)·a}·Φ(h⁻¹xg)`, `g ∈ GL_a`,
`h ∈ GL_b` the representatives, `sq = √q`. -/
noncomputable def om (Pl : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (μ : E → L) (sq : L) (g : GL (Fin a) E)
    (h : GL (Fin b) E) (Φ : Matrix (Fin b) (Fin a) E → L) (x : Matrix (Fin b) (Fin a) E) : L :=
  μ (g : Matrix (Fin a) (Fin a) E).det * (μ (h : Matrix (Fin b) (Fin b) E).det)⁻¹ *
    sq ^ (-(vP Pl (g : Matrix (Fin a) (Fin a) E).det * b)) * sq ^ (vP Pl (h : Matrix (Fin b) (Fin b) E).det * a) *
    Φ (((h⁻¹ : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) * x * (g : Matrix (Fin a) (Fin a) E))

/-- `[x | y]` (the archive's `joinCol`) at sizes `n + c → n′ + c′`: `x` in the first `n` columns, `y` in column `n`, `0`
elsewhere. At the step `m − 2` (`c = 1`, `c′ = 0`) it is exactly the `N_{m−1} × (N_{m−2} + 1)` matrix `[x | y]`. -/
def joinCol {n n' c c' : ℕ} (x : Matrix (Fin n') (Fin n) E) (y : Fin n' → E) :
    Matrix (Fin (n' + c')) (Fin (n + c)) E := fun l s =>
  if h : (l : ℕ) < n' then (if h' : (s : ℕ) < n then x ⟨l, h⟩ ⟨s, h'⟩ else if (s : ℕ) = n then y ⟨l, h⟩ else 0)
  else 0

/-- The index shuffle position `↦` index (spec-6 §6): `fIdx k₀ c n s = s` (`s < k₀`), `n + (s − k₀)`
(`k₀ ≤ s < k₀ + c`), `s − c` otherwise; it moves the `c` extra coordinates to the positions `k₀, …, k₀ + c − 1`. -/
def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c

/-- Its inverse on `[0, n + c)`, index `↦` position: `fPos k₀ c n l = l` (`l < k₀`), `l + c` (`k₀ ≤ l < n`),
`k₀ + (l − n)` (`l ≥ n`). -/
def fPos (k₀ c n l : ℕ) : ℕ := if l < k₀ then l else if l < n then l + c else k₀ + (l - n)

/-- The sharp reordering (spec-6 §6): `symIdx k rS l = l + rS` (`l < k`), `l − k` (`k ≤ l < k + rS`), `l` otherwise;
it lists the positions `[k, k + rS)` first, then `[0, k)`. -/
def symIdx (k rS l : ℕ) : ℕ := if l < k then l + rS else if l < k + rS then l - k else l

/-- The inverse of `symIdx`: `l + k` (`l < rS`), `l − rS` (`rS ≤ l < rS + k`), `l` otherwise. -/
def symIdxInv (k rS l : ℕ) : ℕ := if l < rS then l + k else if l < rS + k then l - rS else l

/-- `bd5 k₀ rS s = rS` if `s = rS + k₀`, else `s` (spec-6 §6). -/
def bd5 (k₀ rS s : ℕ) : ℕ := if s = rS + k₀ then rS else s

/-- The sharp flag `flagS(s) = sclLat(l ↦ scE n (i ↦ i + 1) l + [bd5 s ≤ symIdx(fPos l)])` (spec-6 §6). -/
def flagS (n c : ℕ) (Pl : HeightOneSpectrum (𝓞 E)) (k₀ rS s : ℕ) : Set (Fin (n + c) → E) :=
  sclLat Pl fun l => scE n (fun i => i + 1) l + if bd5 k₀ rS s ≤ symIdx k₀ rS (fPos k₀ c n l) then 1 else 0

/-- The sharp flag vectors `bvecS(s) = bvecG(symIdxInv s)`, with the archive's shuffle `fIdx k₀ c n` (spec-6 §6). -/
noncomputable def bvecS (n c : ℕ) (Pl : HeightOneSpectrum (𝓞 E)) (k₀ rS s : ℕ) : Fin (n + c) → E :=
  bvecG n c Pl (fIdx k₀ c n) (symIdxInv k₀ rS s)

/-- `J` at a place of `SG` for the sharp kernel (spec-6 §6): `JGsym = stabL(lamY(i ↦ i + 1)) ∩ flagU(flagS, bvecS,
r, {r + i·t})`. The frontier's `JS` (`jS`). -/
noncomputable def JGsym (n c : ℕ) (Pl : HeightOneSpectrum (𝓞 E)) (k₀ rS r t : ℕ) : Subgroup (GL (Fin (n + c)) E) :=
  stabL (lamY n c Pl fun i => i + 1) ⊓ flagU (flagS n c Pl k₀ rS) (bvecS n c Pl k₀ rS) r {s | ∃ i, s = r + i * t}

/-- `entB(y)` (spec-6 §1): `M p p′ = y[fIdx k₀ c′ n′ p, fIdx k₀ c n p′]·q^{scE n ex (fIdx k₀ c n p′) −
scE n′ ex (fIdx k₀ c′ n′ p)}`, row `p` a target position, column `p′` a source position; `0` outside
`[0, n′ + c′) × [0, n + c)` (spec-6 §3: else the shuffle aliases out-of-range positions and `PhiGS`, `PhiQ` vanish). -/
noncomputable def entB (Pl : HeightOneSpectrum (𝓞 E)) (k₀ n n' c c' : ℕ) (ex : ℕ → ℤ)
    (y : Matrix (Fin (n' + c')) (Fin (n + c)) E) (p p' : ℕ) : E :=
  if p < n' + c' ∧ p' < n + c then
    qP Pl ^ (scE n ex (fIdx k₀ c n p') - scE n' ex (fIdx k₀ c' n' p)) * entA y (fIdx k₀ c' n' p) (fIdx k₀ c n p')
  else 0

/-- The `k × k` determinant of `M` on the indices `o, …, o + k − 1`. -/
noncomputable def blkDet (M : ℕ → ℕ → E) (o k : ℕ) : E := (Matrix.of fun p p' : Fin k => M (o + p) (o + p')).det

/-- The value of the sharp shape at `SG` before its last factor (the archive's `lamGvS`; spec-13 F4, F7):
`ψ₀(Σ_{l<k₀−1} M_{l,l+1} + Σ_{l<r−k₀−1} M_{k₀+l,k₀+l+1})·∏_{l<i} χ_l(det M_{[r+lt, r+lt+t)²})`, with
`ψ₀(red y) = ψ(y/q)`. `PhiGS` is it times `χ_i(det M_{<a,<a})⁻¹` on its support; at `M = entB(r)` and `i = j` it is
the level-`j` character at `SG` (`SharpChain.IsThetaCol`, the archive's `chrG`). -/
noncomputable def lamGS (Pl : HeightOneSpectrum (𝓞 E)) (ψ : E → L) (χ : ℕ → E → L) (k₀ r t i : ℕ)
    (M : ℕ → ℕ → E) : L :=
  ψ ((∑ l ∈ Finset.range (k₀ - 1), M l (l + 1) + ∑ l ∈ Finset.range (r - k₀ - 1), M (k₀ + l) (k₀ + l + 1)) / qP Pl) *
    ∏ l ∈ Finset.range i, χ l (blkDet M (r + l * t) t)

open Classical in
/-- The sharp kernel shape at `P ∈ SG` (spec-6 §6; `M = entB(x)`, `a = r + i·t`): `0` unless (i) the first `a`
columns are integral, their rows `≥ a` in `P`; (ii) `M_{p′p′} ≡ 1` for `p′ < r`, and `M_{pp′} ≡ 0` for `p < a`,
`p ≠ p′` with `r ≤ p`, `symIdx p′ < symIdx p` or (`p′ = k₀ + rS` and `p < k₀`); (iii) the `t × t` blocks beyond `r`
are block triangular (`M_{pp′} ≡ 0` for `p < a` in a later block than `p′ ≥ r`); then
`lamGS(M)·χ_i(det M_{<a,<a})⁻¹`, i.e.
`ψ₀(Σ_{l<k₀−1} M_{l,l+1} + Σ_{l<r−k₀−1} M_{k₀+l,k₀+l+1})·∏_{l<i} χ_l(det block_l)·χ_i(det M_{<a,<a})⁻¹`, with
`ψ₀(red y) = ψ(y/q)`. -/
noncomputable def PhiGS (Pl : HeightOneSpectrum (𝓞 E)) (ψ : E → L) (χ : ℕ → E → L) (k₀ rS r t i : ℕ)
    (M : ℕ → ℕ → E) : L :=
  if (∀ p p', p' < r + i * t → intAt Pl (M p p') ∧ (r + i * t ≤ p → inP Pl (M p p'))) ∧
      (∀ p' < r, inP Pl (M p' p' - 1) ∧ ∀ p < r + i * t, p ≠ p' →
        (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → inP Pl (M p p')) ∧
      (∀ p p', r ≤ p' → p < r + i * t → (p' - r) / t < (p - r) / t → inP Pl (M p p'))
  then lamGS Pl ψ χ k₀ r t i M * (χ i (blkDet M 0 (r + i * t)))⁻¹
  else 0

open Classical in
/-- The kernel shape at `P ∈ Q` (`M = entB(x)`): `ξ_P(red det M_{<r,<r})` if `M` is integral, its rows `≥ r` in
the first `r` columns lie in `P` and the determinant is a unit; else `0`. -/
noncomputable def PhiQ (Pl : HeightOneSpectrum (𝓞 E)) (ξ : E → L) (r : ℕ) (M : ℕ → ℕ → E) : L :=
  if (∀ p p', intAt Pl (M p p')) ∧ (∀ p p', r ≤ p → p' < r → inP Pl (M p p')) ∧ ¬ inP Pl (blkDet M 0 r)
  then ξ (blkDet M 0 r) else 0

/-- **The factor at one place** `P` of a step from size `n + c` to `n′ + c′`: `volN_P⁻¹·E1(om(Φ_P))(x)`, for the
representatives `g` (source) and `h` (target) at `P`, the group `JS` (read only if `P ∈ SG`), the local parameters and
the kernel shape `Φ_P` at `P`. `XiStd` is its product over the row set; `SharpChain.IsThetaCol` reads it alone at the
places of `Q` (the archive's `surj`). -/
noncomputable def XiStdAt (n n' c c' A : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E)))
    (JS : Subgroup (GL (Fin (n' + c')) E)) (kj : ℕ) (g : GL (Fin (n + c)) E) (h : GL (Fin (n' + c')) E) (ψ μ : E → L)
    (sq : L) (Ph : Matrix (Fin (n' + c')) (Fin (n + c)) E → L) (Pl : HeightOneSpectrum (𝓞 E))
    (x : Matrix (Fin n') (Fin n) E) : L :=
  (((volAt n' c' SG JS kj h Pl)⁻¹ : ℚ) : L) * E1 (Ideal.absNorm Pl.asIdeal) A n n' c c' ψ (om Pl μ sq g h Ph) x

/-- **The local factor** `Ξ(x) = ∏_{P ∈ R} volN_P⁻¹·E1(om(Φ_P))(x_P)` (`XiStdAt` at each `P`) of a step from size
`n + c` to `n′ + c′`, `R` the row set, `x_P` the step's matrix read at `P` (in the frames there, `xiStd`), `g`, `h` the
representatives, `Φ_P` the kernel shapes (`PhiGS ∘ entB` at `SG`, `PhiQ ∘ entB` at `Q`: a parameter, as `JS`; the
canonical ones are `phS`, `phQ`). -/
noncomputable def XiStd (n n' c c' A : ℕ) (R SG : Finset (HeightOneSpectrum (𝓞 E)))
    (JS : HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (n' + c')) E)) (kj : ℕ)
    (g : HeightOneSpectrum (𝓞 E) → GL (Fin (n + c)) E) (h : HeightOneSpectrum (𝓞 E) → GL (Fin (n' + c')) E)
    (ψ μ : HeightOneSpectrum (𝓞 E) → E → L) (sq : HeightOneSpectrum (𝓞 E) → L)
    (Ph : HeightOneSpectrum (𝓞 E) → Matrix (Fin (n' + c')) (Fin (n + c)) E → L)
    (x : HeightOneSpectrum (𝓞 E) → Matrix (Fin n') (Fin n) E) : L :=
  ∏ Pl ∈ R, XiStdAt n n' c c' A SG (JS Pl) kj (g Pl) (h Pl) (ψ Pl) (μ Pl) (sq Pl) (Ph Pl) Pl (x Pl)

/-- `x` is the idele with component `a` at `P` and `1` elsewhere, so that `ν x = ν_P(a)` is the local component of a
character `ν` of the ideles (it stands for the archive's local components, which the library does not define). -/
def IsLocAt (Pl : HeightOneSpectrum (𝓞 E)) (a : E) (x : Ideles E) : Prop :=
  (∀ w ≠ Pl, (x : FiniteAdeleRing (𝓞 E) E) w = 1) ∧
    (x : FiniteAdeleRing (𝓞 E) E) Pl = algebraMap E (Pl.adicCompletion E) a

/-- `χ = ν_P⁻¹` on the `P`-units and `0` off them (the archive's `unitV ∘ red`; spec-6 §4). -/
def ChiOk (Pl : HeightOneSpectrum (𝓞 E)) (ν : Ideles E →* Lˣ) (χ : E → L) : Prop :=
  ∀ a, (Pl.valuation E a = 1 → ∀ x, IsLocAt Pl a x → χ a = ((ν x : Lˣ) : L)⁻¹) ∧ (Pl.valuation E a ≠ 1 → χ a = 0)

open Classical in
/-- The local parameters of a step at the places `R` (spec-6 §4, the canonical instance), for the step's lift
character `ν = μ_{0,i}` and twist `ξ`: `sq² = q`; `ψ` additive on `q⁻¹O_(P)` (the archive's `ψ` is additive only on
`q^{−D}O_P`, `D ≥ 1`) and trivial on `O_(P)`; at `SG`, `ψ(a/q) = ψ₀(red a)` through `σ₀` and `ψ = 1` off `q⁻¹O_(P)`
(`ciPsi`); at `Q = R \ SG` (spec-7 §3d, `twPsiQ`), `ψ(a) = e(⟨xi0·a⟩_P)` on `P^{−dQ}` (`dQ = 2m`): `σ₀(ψ(a)) =
exp(2πi·b/q^{dQ})` for `b ∈ ℤ` with `xi0·a − b/q^{dQ} ∈ O_(P)`, and `ψ(a) = 1` if `a ∉ P^{−dQ}` or no such `b` exists;
`μ = locChar(muq, χ)` with `χ = ν_P⁻¹` on the units at `SG` (`Ch.chi i`, tied to `μ_{0,i}` as in the
archive's `mu0G`) and `ξ_P⁻¹` at `Q` (`resChar⁻¹`), and at every `P ∈ R` `muq = ν_P(q)⁻¹·ξ_P(q)⁻¹`
(`(μ_{0,i})_P(q)⁻¹·qValC⁻¹`, `= ((μ_{0,i}ξ)_P(q))⁻¹`, reading `qValC(ξ, P)` as `ξ_P(q)`; spec-7 §3b–3c; at the
untwisted level `ξ = 1`). Meant for L7. -/
def LocOk (σ₀ : L →+* ℂ) (xi0 : E) (dQ : ℕ) (R SG : Finset (HeightOneSpectrum (𝓞 E))) (ν ξ : Ideles E →* Lˣ)
    (ψ μ : HeightOneSpectrum (𝓞 E) → E → L) (sq : HeightOneSpectrum (𝓞 E) → L) (χ : HeightOneSpectrum (𝓞 E) → E → L) :
    Prop :=
  ∀ Pl ∈ R, sq Pl ^ 2 = (Ideal.absNorm Pl.asIdeal : L) ∧
    (∀ y z, intAt Pl (qP Pl * y) → intAt Pl (qP Pl * z) → ψ Pl (y + z) = ψ Pl y * ψ Pl z) ∧
    (∀ y, intAt Pl y → ψ Pl y = 1) ∧
    (Pl ∈ SG → (∀ y : 𝓞 E, σ₀ (ψ Pl ((y : E) / qP Pl)) = psi0 xi0 Pl (Ideal.Quotient.mk Pl.asIdeal y)) ∧
      ∀ y, ¬ intAt Pl (qP Pl * y) → ψ Pl y = 1) ∧
    (Pl ∉ SG → ∀ y, (∀ b : ℤ, intAt Pl (qP Pl ^ dQ * y) → intAt Pl (xi0 * y - b / qP Pl ^ dQ) →
        σ₀ (ψ Pl y) = Complex.exp (2 * Real.pi * Complex.I * b / (Ideal.absNorm Pl.asIdeal : ℂ) ^ dQ)) ∧
      ((¬ intAt Pl (qP Pl ^ dQ * y) ∨ ∀ b : ℤ, ¬ intAt Pl (xi0 * y - b / qP Pl ^ dQ)) → ψ Pl y = 1)) ∧
    ChiOk Pl (if Pl ∈ SG then ν else ξ) (χ Pl) ∧
    ∃ muq, μ Pl = locChar Pl muq (χ Pl) ∧
      ∀ x, IsLocAt Pl (qP Pl) x → muq = ((ν x : Lˣ) : L)⁻¹ * ((ξ x : Lˣ) : L)⁻¹

end Kernel

section LevelQ

variable {E L : Type*} [Field E] [NumberField E] [Field L] {n c : ℕ}

variable (n c) in
/-- **The archive's normal form of a representative at `P ∈ Q`** (`TwNF`; spec-12 F1, F6): `h·O_(P)^{n+c} = Λ_{ν,z}`,
the `v` with `v_l − v_n·z_l ∈ O_(P)` (`l < n`) and `q^{−ν_i}·v_{n+i} ∈ O_(P)` (`i < c`), for some `z ∈ O_(P)^n` and
`ν ∈ [−j, 0]^c`; equivalently `h ∈ n_z·diag(1_n, q^ν)·GL_{n+c}(O_(P))`, `n_z : f₀ ↦ f₀ + z` (`f₀ = e_n`). It implies the
archive's `TwBdd` (`O ⊆ hO ⊆ q^{−j}O`); with `c = 0` it says `h ∈ GL_n(O_(P))`. For `SharpChain.IsThetaCol`. -/
def TwNF (Pl : HeightOneSpectrum (𝓞 E)) (j : ℕ) (h : GL (Fin (n + c)) E) : Prop :=
  ∃ (ν : Fin c → ℤ) (z : Fin n → E), (∀ l, intAt Pl (z l)) ∧ (∀ i, -(j : ℤ) ≤ ν i ∧ ν i ≤ 0) ∧
    ∀ v : Fin (n + c) → E,
      (∀ l, intAt Pl (Matrix.mulVec ((h⁻¹ : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) v l)) ↔
      (∀ l : Fin n, intAt Pl (v (Fin.castAdd c l) - (if hc : n < n + c then v ⟨n, hc⟩ else 0) * z l)) ∧
        ∀ i : Fin c, intAt Pl (qP Pl ^ (-ν i) * v (Fin.natAdd n i))

/-- The top-left `n × n` block `A(r)` of `r = [[A, B], [0, U]]`. -/
def blkA (r : GL (Fin (n + c)) E) : Matrix (Fin n) (Fin n) E :=
  fun a b => (r : Matrix (Fin (n + c)) (Fin (n + c)) E) (Fin.castAdd c a) (Fin.castAdd c b)

/-- `n1Arg(r) = Σ_{i < c−1} r_{n+i, n+i+1}` (the archive's `n1Arg`): the superdiagonal of the unipotent block `U`
(`entA` is `0` out of range, so the last term drops). -/
def n1Arg (r : GL (Fin (n + c)) E) : E :=
  ∑ i : Fin c, entA (r : Matrix (Fin (n + c)) (Fin (n + c)) E) (n + i) (n + i + 1)

variable (n c) in
/-- `prX(C)` (the archive's `prX`): the blocks `A(r)` of the `r ∈ C`. For `C ≤ R1` (the archive's `prCat =
prX(Cbe(J, h))` at `Q`, `prX(R1 ∩ J)` at `SG`) they form a group, as `r ↦ A(r)` is multiplicative on the block upper
triangular `R1` (the closure adds nothing). -/
def prX (C : Subgroup (GL (Fin (n + c)) E)) : Subgroup (GL (Fin n) E) :=
  Subgroup.closure {g | ∃ r ∈ C, blkA r = g}

variable (n c) in
/-- **The level at `P ∈ Q` is pinned** (the archive's `grpQ`, `chrQ`, `chiInv`; spec-11 §2, spec-12 F6): the group is
`H = prX(R1 ∩ h·JQ(kj)·h⁻¹) ∩ GL_n(O_(P))` (in `glInt`), and its character is
`λ(g) = ψ_P(n1Arg r)⁻¹·ξ_P(det(h⁻¹rh)_{[kj,n)²})⁻¹` for every `r ∈ R1 ∩ h·JQ(kj)·h⁻¹` with `A(r) = g`, with
`χ = ξ_P⁻¹` on the `P`-units and `0` off them (`LocOk` at `Q`; the archive's `unitV`). For the representatives `h` in
the normal form `TwNF` the `ψ_P` factor is not `1` in general (`r` need not be integral), and `H` contains
`1 + P^{j+1}·M_n(O_(P))` with trivial character but not `1 + P·M_n(O_(P))` (spec-12 F6, the archive's
`conj_extE_cong`): so the classes carry lattice frames at `Q` (`ThetaChain.DecoF`). For `SharpChain.IsThetaCol`, at the
levels `1 ≤ j < m` (level `0` is `ChIdx.zero_Q`). -/
def LevQOk (Pl : HeightOneSpectrum (𝓞 E)) (kj : ℕ) (h : GL (Fin (n + c)) E) (ψ χ : E → L)
    (H : Subgroup (glInt n Pl)) (lam : H →* Lˣ) : Prop :=
  H = (prX n c (Cbe n c (JQ n c Pl kj) h)).subgroupOf (glInt n Pl) ∧ ∀ g : H, ∀ r ∈ Cbe n c (JQ n c Pl kj) h,
    blkA r = ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) →
    ((lam g : Lˣ) : L) = (ψ (n1Arg r))⁻¹ *
      χ (blkDet (entA ((h⁻¹ * r * h : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E)) kj (n - kj))

/-- `ḡ` is the reduction mod `P` of `g` (the archive's `red_w`): every entry of `g` is congruent mod `P·O_(P)` to an
element of `O_E` lifting the entry of `ḡ` (so `g` is `P`-integral). For `LevGOk`. -/
def IsRed (Pl : HeightOneSpectrum (𝓞 E)) (g : Matrix (Fin n) (Fin n) E)
    (gb : Matrix (Fin n) (Fin n) (𝓞 E ⧸ Pl.asIdeal)) : Prop :=
  ∀ a b, ∃ y : 𝓞 E, Ideal.Quotient.mk Pl.asIdeal y = gb a b ∧ inP Pl (g a b - y)

variable (n c) in
/-- **The level at `SG` is pinned** (the archive's `grpG` with `levG = colLevSym`, audit 11): the representatives are
`h = 1` at `SG`, and the level group is `∏_{w ∈ SG} red_w(prX(R1 ∩ J_w))`, `J_w` the level's group at `w` (`jS`, the
sharp `JGsym`): `ḡ` is in it iff at every `w ∈ SG`, `ḡ_w` is the reduction (`IsRed`) of some `A ∈ prX(R1 ∩ J_w)`.
Its character (`chrG`, read by no factor) is pinned beside it in `SharpChain.IsThetaCol` through `lamGS`. For
`SharpChain.IsThetaCol`, at the levels `1 ≤ j < m` (level `0` is `ChIdx.zero_grp`). -/
def LevGOk {SG : Finset (HeightOneSpectrum (𝓞 E))} (J : HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (n + c)) E))
    (Λ : Subgroup (∀ w : SG, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) : Prop :=
  ∀ gb, gb ∈ Λ ↔ ∀ w : SG, ∃ g ∈ prX n c (R1 n c ⊓ J w.1),
    IsRed w.1 (g : Matrix (Fin n) (Fin n) E) (gb w : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal))

end LevelQ

section Pin

variable {E L : Type*} [Field E] [NumberField E] [IsCMField E] [Field L] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {τ : Φ → (E →+* L)}

/-- The canonical sharp kernel shape of step `j` at `P ∈ SG` (spec-6 §6, `PhiAt` with `sharp = true`): `PhiGS ∘ entB`
with `k₀ = k`, `rS = m/2 − 1`, `r = k + m − 1`, `ex = (i ↦ i + 1)`, `ψ_P` and the characters `χ_l` of the steps `l ≤ j`.
The frontier's `Ph`. -/
noncomputable def phS (D : Data τ) (m k t : ℕ) (ψ χ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (j : ℕ)
    (Pl : HeightOneSpectrum (𝓞 E)) (y : Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E) :
    L :=
  PhiGS Pl (ψ j Pl) (fun l => χ l Pl) k (m / 2 - 1) (k + m - 1) t j
    (entB Pl k (D.n j) (D.n (j + 1)) (m - 1 - j) (m - 1 - (j + 1)) (fun i => i + 1) y)

/-- The canonical kernel shape of step `j` at `P ∈ Q` (spec-7 §3e, `PhiAt` off `SG`): `PhiQ ∘ entB` with `k₀ = k`,
`r = k + m − 1`, `ex = 0`, and `ξ_P = χ_j⁻¹` on the units (`LocOk`: `χ_j = ξ_P⁻¹` there). The frontier's `Ph` at `Q`. -/
noncomputable def phQ (D : Data τ) (m k : ℕ) (χ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (j : ℕ)
    (Pl : HeightOneSpectrum (𝓞 E)) (y : Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E) :
    L :=
  PhiQ Pl (fun a => (χ j Pl a)⁻¹) (k + m - 1) (entB Pl k (D.n j) (D.n (j + 1)) (m - 1 - j) (m - 1 - (j + 1)) 0 y)

/-- The canonical sharp group of level `j` at `P ∈ SG` (spec-6 §4, §6, `Jat` with `sharp = true`):
`JGsym(k, m/2 − 1, k + m − 1, t)` at size `N_j + c_j`. The frontier's `JS`. -/
noncomputable def jS (D : Data τ) (m k t j : ℕ) (Pl : HeightOneSpectrum (𝓞 E)) :
    Subgroup (GL (Fin (D.n j + (m - 1 - j))) E) :=
  JGsym (D.n j) (m - 1 - j) Pl k (m / 2 - 1) (k + m - 1) t

open Classical in
/-- `XiStd` at step `j < m − 1` of `D`: sizes `N_j + c_j → N_{j+1} + c_{j+1}` (`c_j = m − 1 − j`), representatives
`g = h_{j,c}`, `h = h_{j+1,c′}`, `J = JS` at `SG` and `JQ(k + j + 1)` at `Q = R \ SG`; local parameters per step. As in
the archive's `XiEntry`, `x` is read at each `P` in the frames of the representatives, `inFr(fr_P(c), fr_P(c′), x)`
(`ThetaChain.DecoF.frAt`: the frame lifts at `SG`, the lattice frames at `Q`, spec-11 A0; none elsewhere), times the
level-`T` indicator `phiT(c, c′, x)`. -/
noncomputable def xiStd (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L)
    (j : ℕ) (c : Cls D.n D.ST D.SG D.Q D.β D.Λ j) (c' : Cls D.n D.ST D.SG D.Q D.β D.Λ (j + 1)) :
    Matrix (Fin (D.n (j + 1))) (Fin (D.n j)) E → L := fun x =>
  (if phiT c.2.rep.d c'.2.rep.d x then 1 else 0) *
    XiStd (D.n j) (D.n (j + 1)) (m - 1 - j) (m - 1 - (j + 1)) A R D.SG (JS (j + 1)) (k + (j + 1)) (h j c.1)
      (h (j + 1) c'.1) (ψ j) (μ j) (sq j) (Ph j) fun Pl => inFr (c.2.rep.frAt Pl) (c'.2.rep.frAt Pl) x

/-- **The coupled factor of step `j = m − 2`** (spec-10 F3, F5 items 3 and 5; the archive's `XiCpl1`, the coset `Y` in
its collapsed form `ȳ`): `∏_{P ∈ SG} XiStd_P(x)` (at `SG` the coset sum has one live coset, `y ≡ q⁻¹e_k`, which `E1`
integrates; `volN = 1` at level `m − 1`) times `∏_{P ∈ R} q_P^{−(m−1)N_{m−1}}·om_P(g = h_{j,c}, h = 1, Φ_P)([x | ȳ_P])`
over the places `R = Q \ SG`, `ȳ_P ∈ (O/P^{m−1})^{N_{m−1}}` lifted to `O_E` (`PsiAt`: no `E1`, no `volN`). **The
collapse** (spec-10 F3, redone for the representatives in `TwNF`): with `g = n_z·diag(1, q^ν)·κ`, `κ ∈ GL(O_(P))`,
`ν ∈ [−(m−2), 0]`, `[x | y′]·g = [x | q^ν(xz + y′)]·κ`, so `PsiAt` vanishes unless `x` and `y′` are integral and depends
on `y′` only mod `q^{1−ν}O ⊇ q^{m−1}O`; the archive's sum over `Y ∈ q^{−m}O/q^mO` with the `ftY` weights
`q^{−m·N}ψ_P(−η·y′)` is then the sum over `ȳ` mod `P^{m−1}` with `q^{−(m−1)N}` here and `1[q^{m−1}η ∈ O_(P)]·ψ_P(−η·ȳ)`
in `xiTop` (for integral `g` it reduces to the residue form). As in `xiStd`, `x` is read in the frames of `c`, `c′`
(`ȳ_P` is in the frame of `c′`), and `phiT(c, c′, x)` is a factor (that of `xiStd`). -/
noncomputable def xiCpl (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L)
    (j : ℕ) (c : Cls D.n D.ST D.SG D.Q D.β D.Λ j) (c' : Cls D.n D.ST D.SG D.Q D.β D.Λ (j + 1))
    (y : ∀ P : R, Fin (D.n (j + 1)) → 𝓞 E ⧸ P.1.asIdeal ^ (j + 1)) (x : Matrix (Fin (D.n (j + 1))) (Fin (D.n j)) E) :
    L :=
  xiStd D m A k D.SG h JS ψ μ sq Ph j c c' x *
    ∏ P : R, ((Ideal.absNorm P.1.asIdeal : L) ^ ((j + 1) * D.n (j + 1)))⁻¹ *
      om P.1 (μ j P.1) (sq j P.1) (h j c.1 P.1) 1 (Ph j P.1)
        (joinCol (inFr (c.2.rep.frAt P.1) (c'.2.rep.frAt P.1) x) fun i => (((y P i).out : 𝓞 E) : E))

open Classical in
/-- **The top factor** (spec-10 F2, F5 items 4–5; the archive's `XiCpl2`, the coset as in `xiCpl`) of step
`j = m − 1`, from the class `c` to a decorated lattice `d′` of rank `N_m` (L7: the lift `tilQ` of the row point `d`),
on `x′ ∈ M_{N_m × N_{m−1}}`. At each `P`, `x′` is read as in the archive (`top_P`, `η_P`; spec-10 F1):
`top = fr_P(d)⁻¹·x′_{<N_m−1}·fr_P(c)` (the first `N_m − 1` rows, in the row point's frames `frd`: L7 passes its frame
lifts) and `η = π⁻¹·x′_last·fr_P(c)` (the last row, `π = conj(tz)`), not through a frame lift of `d′`: that lift is
fixed only up to `1 + P·M(O_(P))`, which moves `η`, read to precision `q^{−(m−1)}` at `Q`, and through it `top`. Then:
`phiT(c, d′, x′)·∏_{P ∈ SG} PhiTop_P(top)·1[η ∈ O_(P)]·ψ_P(−η_k/q_P)` times
`∏_{P ∈ R} PhiTop_P(top)·1[q_P^{m−1}·η ∈ O_(P)]·ψ_P(−η·ȳ_P)` (`R = Q \ SG`, `ȳ_P` mod `P^{m−1}`, as in `xiCpl`).
`PhiTop_P` is `PhiGS ∘ entB` at `SG`
(`i = m − 1`, `ex = (i ↦ i + 1)`) and `PhiQ ∘ entB` at `Q` (`ex = 0`, `ξ_P = χ_{m−1}⁻¹`), at sizes
`N_{m−1} + 0 → (N_m − 1) + 0`; its values are `0` or roots of unity at `SG`. -/
noncomputable def xiTop (D : Data τ) (m k t : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    {SF : Finset (HeightOneSpectrum (𝓞 E))} (ψ χ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (j : ℕ)
    (c : Cls D.n D.ST D.SG D.Q D.β D.Λ j) (d' : Deco E (D.n (j + 1)) D.ST SF)
    (frd : HeightOneSpectrum (𝓞 E) → Matrix (Fin (D.n (j + 1) - 1)) (Fin (D.n (j + 1) - 1)) E) (π : E)
    (y : ∀ P : R, Fin (D.n j) → 𝓞 E ⧸ P.1.asIdeal ^ j) (x : Matrix (Fin (D.n (j + 1))) (Fin (D.n j)) E) : L :=
  let top : HeightOneSpectrum (𝓞 E) → Matrix (Fin (D.n (j + 1) - 1 + 0)) (Fin (D.n j + 0)) E :=
    fun P l s => entA ((frd P)⁻¹ * Matrix.of fun (l : Fin (D.n (j + 1) - 1)) (s : Fin (D.n j)) =>
      entA (x * c.2.rep.frAt P) l s) l s
  let η : HeightOneSpectrum (𝓞 E) → ℕ → E := fun P s => π⁻¹ * entA (x * c.2.rep.frAt P) (D.n (j + 1) - 1) s
  (if phiT c.2.rep.d d' x then 1 else 0) *
    ((∏ P ∈ D.SG, PhiGS P (ψ j P) (fun l => χ l P) k (m / 2 - 1) (k + m - 1) t j
        (entB P k (D.n j) (D.n (j + 1) - 1) 0 0 (fun i => i + 1) (top P)) *
      if ∀ s, intAt P (η P s) then ψ j P (-η P k / qP P) else 0) *
    ∏ P : R, PhiQ P.1 (fun a => (χ j P.1 a)⁻¹) (k + m - 1) (entB P.1 k (D.n j) (D.n (j + 1) - 1) 0 0 0 (top P.1)) *
      if ∀ s, intAt P.1 (qP P.1 ^ j * η P.1 s) then
        ψ j P.1 (-∑ s : Fin (D.n j), η P.1 s * (((y P s).out : 𝓞 E) : E)) else 0)

/-- **The local factors are pinned** (spec-3 §1, spec-10 F5): `Ξ_j = XiStd` at the generic steps `j < m − 2` (the
archive's `mat`), with the representatives `h` (the `ChIdx` bundle's), the groups `JS` and the local parameters passed
in. Step `m − 2` is the coupled `xiCpl` and step `m − 1` the top `xiTop`. The frontier (L7, `IsThetaCol`) uses it with
`JS = jS`, `Ph = phS` at `SG` and `phQ` at `Q`, `A = m + 1` and `LocOk`. -/
def XiFull (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L) : Prop :=
  ∀ j, j + 2 < m → ∀ c c', D.Xi j c c' = xiStd D m A k R h JS ψ μ sq Ph j c c'

/-- **The scale of `Ξ_j` is pinned** (spec-3 §1, verdict): for `j < m − 2`, `Ξ_j(c, c′)` at the trivial coset is
`XiStd` there up to a unit `u` with `|u| = 1` at every complex place (harmless for slopes by the product formula).
The weaker pin the frontier used before spec-6; kept for `XiFull.scale`. -/
def XiScale (D : Data τ) (m A k : ℕ) (R : Finset (HeightOneSpectrum (𝓞 E)))
    (h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m - 1 - j))) E)
    (JS : ∀ j, HeightOneSpectrum (𝓞 E) → Subgroup (GL (Fin (D.n j + (m - 1 - j))) E))
    (ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : ℕ → HeightOneSpectrum (𝓞 E) → L)
    (Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
      Matrix (Fin (D.n (j + 1) + (m - 1 - (j + 1)))) (Fin (D.n j + (m - 1 - j))) E → L) : Prop :=
  ∀ j, j + 2 < m → ∀ c c', ∃ u : L, (∀ σ : L →+* ℂ, ‖σ u‖ = 1) ∧
    D.Xi j c c' 0 = xiStd D m A k R h JS ψ μ sq Ph j c c' 0 * u

omit [Fintype Φ] [DecidableEq Φ] in
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
