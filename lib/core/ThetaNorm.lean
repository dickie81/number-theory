import Mathlib
import ThetaChain

/-!
# The normalisation of the base theta

Pins the free `ℂ^×` scale of `ThetaChain.ThetaStd.θ` for the sharp frontier (spec-3 §2, option (A), the archive's
exact condition). The library's `θ_std` on `Amb Φ a b` is the archive's `thZero(a, b) = tensPow θ₀`,
`θ_std(z) = ∏_{i<b, j<a} θ₀(z_{·ij})` (`tensPow`), and `θ₀` on `ℂ^Φ` is pinned by a fourth-power identity:
`θ₀ ∈ Th(Λ_M)` and `θ₀^{⊗4} = κ·(Iop(stdLat, g(Λ_M⁴)) F0) ∘ g` (`IsTheta0`), with

* `th0(z) = U_t σ*(z) / U_t σ*(0)`, `t = ω₀/2`, the one-variable theta normalised by `th0(0) = 1` (`th0`, `th0_zero`);
* `F0(z) = ∏_i th0(z_i)` on `ℂ^{Fin 4 × Φ}` (`F0`), `θ^{⊗4}(v) = ∏_{k<4} θ(v_k)` (`tens4`, `slice`);
* `stdLat = L^{Fin 4 × Φ}` for the one-variable lattice `L` (`stdLat4`), `Λ_M⁴` (`pow4`).

**Choices.** The form of `θ₀` is the library's `Hf s` on each slice (it must be, as `θ_std = tensPow θ₀` lives in
`Th(Hf s)`), so `g` is an `Hf s`-isometry of `ℂ^{Fin 4 × Φ}`. The normalised sigma `σ*`, the point `t = ω₀/2`, the
lattices `L` and `Λ_M`, the isometry `g` and the phase `κ` are not transcribed (the archive's `sgStar`, `gC` and
`KapChoice.kappa` need the CM elliptic curve and the split-prime data): they are the fields of `Pin`, with the stated
properties `U_t σ*(0) ≠ 0` (so `th0(0) = 1`), `g` an isometry and `|κ| = 1`.

**Freedom left.** Given a `Pin`, `θ₀` is unique up to `ζ⁴ = 1` (spec-3 §2, `ThetaVector`), and `ζ^{ab} = 1` for even
`a, b`, so `θ_std` is pinned. Since `κ` is only constrained by `|κ| = 1`, the remaining freedom of the frontier is a
unimodular phase, which does not change slopes; the `ℂ^×` (in particular `ℚ^×`) scale is gone.

**Sanity theorems:** `th0_zero`, `F0_zero`.
-/

namespace ThetaNorm

open NumberField ThetaChain HermClasses

section Base

/-- The one-variable theta `th0(z) = U_t σ*(z) / U_t σ*(0)` on `ℂ` (as `Unit → ℂ`), for the form `Hf s`. -/
noncomputable def th0 (s : ℝ) (σ : ℂ → ℂ) (t z : ℂ) : ℂ :=
  opU s (fun _ : Unit => t) (fun w => σ (w ())) (fun _ => z) / opU s (fun _ : Unit => t) (fun w => σ (w ())) 0

/-- The product theta `F0(z) = ∏_i th0(z_i)`. -/
noncomputable def F0 {ι : Type*} [Fintype ι] (s : ℝ) (σ : ℂ → ℂ) (t : ℂ) (z : ι → ℂ) : ℂ := ∏ i, th0 s σ t (z i)

variable {Φ : Type*} [Fintype Φ]

/-- The slice `v ↦ v_k = (v(k, p))_p` of `ℂ^{Fin 4 × Φ}`. -/
def slice (k : Fin 4) : (Fin 4 × Φ → ℂ) →+ (Φ → ℂ) :=
  (LinearMap.funLeft ℂ ℂ (fun p : Φ => (k, p))).toAddMonoidHom

/-- The fourth tensor power `θ^{⊗4}(v) = ∏_{k<4} θ(v_k)`. -/
noncomputable def tens4 (θ : (Φ → ℂ) → ℂ) (v : Fin 4 × Φ → ℂ) : ℂ := ∏ k : Fin 4, θ (slice k v)

/-- The lattice `Λ⁴ = {v : v_k ∈ Λ for all k}`. -/
def pow4 (Λ : AddSubgroup (Φ → ℂ)) : AddSubgroup (Fin 4 × Φ → ℂ) := ⨅ k, Λ.comap (slice k)

/-- The standard lattice `L^{Fin 4 × Φ}` of `F0`. -/
def stdLat4 (Lc : AddSubgroup ℂ) : AddSubgroup (Fin 4 × Φ → ℂ) := AddSubgroup.pi Set.univ fun _ => Lc

/-- The tensor power `θ_std(z) = ∏_{i<b, j<a} θ₀(z_{·ij})` on `Amb Φ a b` (the archive's `tensPow`). -/
noncomputable def tensPow {a b : ℕ} (θ₀ : (Φ → ℂ) → ℂ) (z : Amb Φ a b) : ℂ :=
  ∏ i : Fin b, ∏ j : Fin a, θ₀ fun p => z (p, i, j)

variable (Φ) in
/-- The data that pin `θ₀` for the form `Hf s`, not transcribed (spec-3 §2): the one-variable lattice `L`, the
normalised sigma `σ*`, the point `t = ω₀/2` with `U_t σ*(0) ≠ 0`, the lattice `Λ_M`, an `Hf s`-isometry `g` (the
archive's `gC`) and the phase `κ` (`KapChoice.kappa`) with `|κ| = 1`. Meant for the frontier, which passes one. -/
structure Pin (s : ℝ) where
  /-- The one-variable lattice `L`. -/
  Lc : AddSubgroup ℂ
  /-- The normalised sigma `σ*`. -/
  σ : ℂ → ℂ
  /-- The 2-torsion point `t = ω₀/2`. -/
  t : ℂ
  /-- `U_t σ*(0) ≠ 0`, so `th0(0) = 1`. -/
  ne : opU s (fun _ : Unit => t) (fun w => σ (w ())) 0 ≠ 0
  /-- The lattice `Λ_M` of `θ₀`. -/
  Λ : AddSubgroup (Φ → ℂ)
  /-- The isometry `g : blk4(H₁) → stdH`. -/
  g : (Fin 4 × Φ → ℂ) ≃ₗ[ℂ] (Fin 4 × Φ → ℂ)
  g_isom : ∀ z w, Hf s (g z) (g w) = Hf s z w
  /-- The phase `κ`. -/
  κ : ℂ
  norm_κ : ‖κ‖ = 1

/-- The archive's `IsThM`: `θ₀ ∈ Th(Λ_M)` and `θ₀^{⊗4} = κ·(Iop(stdLat, g(Λ_M⁴)) F0) ∘ g`. -/
def IsTheta0 {s : ℝ} (sd : ℝ) (D : Pin Φ s) (θ₀ : (Φ → ℂ) → ℂ) : Prop :=
  θ₀ ∈ Th s sd D.Λ ∧
    tens4 θ₀ = D.κ • (Iop s sd (stdLat4 D.Lc) ((pow4 D.Λ).map D.g.toLinearMap.toAddMonoidHom) (F0 s D.σ D.t) ∘ D.g)

/-- `th0(0) = 1`. -/
theorem th0_zero {s : ℝ} (D : Pin Φ s) : th0 s D.σ D.t 0 = 1 := div_self D.ne

/-- `F0(0) = 1` (spec-3 §2, as in the archive's `ProductThetaMem`). -/
theorem F0_zero {ι : Type*} [Fintype ι] {s : ℝ} (D : Pin Φ s) : F0 s D.σ D.t (0 : ι → ℂ) = 1 :=
  Finset.prod_eq_one fun _ _ => th0_zero D

end Base

section Std

variable {E L : Type*} [Field E] [NumberField E] [Field L] [IsCMField E] {Φ : Type*} [Fintype Φ] [DecidableEq Φ]
  {τ : Φ → (E →+* L)} {P : TP E L Φ} {a b : ℕ}

/-- The base theta is normalised (spec-3 §2, option (A), the archive's exact condition): `θ_std = tensPow θ₀` for a
`θ₀` with `θ₀^{⊗4} = κ·(Iop(stdLat, g(Λ_M⁴)) F0) ∘ g` (`IsTheta0`), for the pinning data `D`. This kills the `ℂ^×`
scale; what remains free is the phase `κ` of `D` (`|κ| = 1`), a unimodular phase, which does not change slopes, and
a `ζ⁴ = 1` that `tensPow` absorbs for even `a, b`. Meant for the frontier. -/
def _root_.ThetaChain.ThetaStd.Normalised (D : Pin Φ P.s) (T : ThetaStd τ P a b) : Prop :=
  ∃ θ₀, IsTheta0 P.sd D θ₀ ∧ T.θ = tensPow θ₀

end Std

end ThetaNorm
