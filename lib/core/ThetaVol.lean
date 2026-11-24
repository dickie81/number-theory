import Mathlib
import ThetaChain

/-!
# The local volumes of the theta kernels (spec-3 §1)

The local factor `Ξ_j` of a step `j < m − 1` is `∏_{P ∈ S} volN_P(j)⁻¹ · E1(om(Φ_P))`, and the `E1 ∘ om ∘ Φ` part has a
fixed scale; so the volumes `volN_P(j)` carry the scale of `Ξ_j`. This module defines them and the predicate
`XiVolPinned` with which the sharp frontier (L7) pins the scale of the data's `Ξ`.

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

end Pin

end ThetaVol
