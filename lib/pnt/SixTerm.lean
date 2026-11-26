import ZetaPair

/-!
# The six-term interface below the frame inequality — CONDITIONAL on the half-plane

A step of the library's proof of the Riemann hypothesis for `ζ` and every Dirichlet `L`-function
(`docs/rh-rebuild.md`, "Next"): the algebra of the archive's `ch_top` below the frame inequality. Six numeric
inequalities about the words of each translate give the gain (G) of `LatticeData`, and with it `PairBound`.

**The data** (`SixTermData`), at each translate `u` of the kernel `A₀` of `κ`:
* a frame (`SlopeFrame.Frame`), whose words `ω` have sources `N_ω` mapping to one target `C_u` with heights `h_ω`,
  and a frame loss `L_u ≥ s_u − μ(C_u)`, at the rank-weighted mean `s_u` of `μ(N_ω) − h_ω` (`SlopeFrame.Frame.mean`):
  the conclusion of the frame inequality, which a frame meeting its hypotheses gives
  (`SlopeFrame.Frame.Spread.frame_le`); `HermitianLattice.frame` supplies the archive's own frames;
* for each word, the slope `μ(M_ω)` of its lattice of forms, its split primes `Ee_ω` and its auxiliary prime `T_ω`;
* for the translate, the vanishing gain `Ga` at the inert places, the forced vanishing `Fo`, a scale `v > 0`,
  `lg = log(g₀g₁)`, and one slack `c_i` for each inequality.

With `φ(y) = y log y − y`, `log Ω = γ + log(π/v) − Re L′/L(1, χ_d)` (`Setting.logΩ`),
`Λ_u = Σ_{j<m} |Φ|⁻¹ Σ_ρ log(w_{u,j}(ρ)·v/π) + m·lg` (`Setting.lam`) and
`MAIN_ω = Σ_t [m(φ(a_t) − a_t log Ω) − a_t log T_ω]` (`Setting.mainW`), the six are:
* **G1**, the vanishing: `μ(N_ω) ≥ μ(M_ω) + Ga + Fo − Ee_ω − c₁`;
* **G2**, the forms: `μ(M_ω) ≥ −c₂`;
* **G3**, the target: `μ(C_u) + h_ω − Fo ≤ MAIN_ω + c₃`;
* **G4**, the auxiliary primes: `Λ_u − c₄ ≤ log T_ω`;
* **G5**, the split primes: `Ee_ω − m(Σ_t a_t)·lg ≤ c₅`;
* **G6**, the gain: `Σ_t Σ_j ASK(a_t, t, w_{u,j}) − Ga ≤ c₆`.

**The key identity** (`Setting.key_identity`):
`Σ_t m(φ(a_t) − a_t log Ω) − (Σ_t a_t)·Λ_u + m(Σ_t a_t)·lg = Σ_t Σ_j MAIN(a_t, w_{u,j})`, with the library's `MAIN`.
The terms in `log(π/v)` cancel.

**Summing.** `Fo` cancels between G1 and G3, `(Σ_t a_t)·log T_ω` between G3 and `Σ_t a_t` times G4, and
`m(Σ_t a_t)·lg` between G4 and G5. With G2, G6 and the key identity, every word has
`μ(N_ω) − h_ω − μ(C_u) ≥ gap(u) − c_u` (`SixTermData.gap_le_word`), with `c_u = c₁ + c₂ + c₃ + (Σ_t a_t)·c₄ + c₅ + c₆`
(`SixTermData.slack`). The rank-weighted mean over the words gives `s_u − μ(C_u) ≥ gap(u) − c_u`
(`SixTermData.gap_le_mean`), which is (G) of `LatticeData` with `E = Σ_{u ∈ A₀} c_u`. One budget,
`Σ_{u ∈ A₀} (c_u + L_u) ≤ |A₀|·x^{4ε}·Σ_t a_t`, is (Z). So six-term data are lattice data (`SixTermData.toLatticeData`),
and the frontier `SixTermBound`, `PairBound` with six-term data, gives the Riemann hypothesis for `ζ` and every
Dirichlet `L`-function (`rhAndGRH_of_sixTermBound`).

**Against the archive:**
* G5 is one-sided. The archive also uses its other side, with upper bounds on `μ_max(M_ω)` and `μ_max(N_ω)`, to get
  the range condition (R) of the frame inequality. Here only the frame inequality's conclusion is asked, the loss
  `L_u`; how it is bounded is the construction's.
* The losses `Lo_ω` of the words in G1, and the archive's slack sizes, merge into one slack per inequality. All slacks
  go into one budget with the frame losses.
* The frames are abstract, so the frontier's strength does not depend on the lattices chosen.

**What this frontier means.** Like `PairBound`, it is still satisfied by rank-one witnesses whenever the averaged gap
bound holds (`docs/rh-rebuild.md`, "The construction, measured"). Take at each translate one word, with `N = C` of rank
one, the identity of height `0` and loss `L = 0`, and put `μ(M) = 0`, `Ga = Σ_t Σ_j ASK`, `lg = Ee = 0`,
`log T = Λ_u`, `Fo` that makes G1 exact, `c₃ = gap(u)` and every other slack `0`. Then G3 holds with equality by the
key identity, `s_u = μ(C_u)`, and the budget is the averaged gap bound. The value of the module is the formalised
algebra of `ch_top`, about 3,000 lines of the archive. Content needs the objects defined: the canonical theta datum,
with its forms, periods and target.

**CONDITIONAL.** `rhAndGRH_of_sixTermBound` goes through `rhAndGRH_of_pairBound`, so it rests on the half-plane
`Re s > 11/12` for `ζ` and every Dirichlet `L`-function (`Eis.LFunction_ne_zero_of_re_gt`), an input formalised in the
library that no referee has read (see `formalisations/openai-half-plane.md`).
-/

open DirichletCharacter

namespace SlopeFrame

/-- **Slope times rank is degree**: `(deg ⊤/rk ⊤)·rk ⊤ = deg ⊤`, also at rank `0`, where `⊤ = ⊥`. -/
theorem SlopeLattice.slope_mul_rk {L : Type*} [Lattice L] [BoundedOrder L] (X : SlopeLattice L) :
    X.deg ⊤ / X.rk ⊤ * X.rk ⊤ = X.deg ⊤ :=
  div_mul_cancel_of_imp fun h => by
    obtain h' | h' := eq_bot_or_bot_lt (⊤ : L)
    · rw [h', X.deg_bot]
    · have := X.rk_strictMono h'
      rw [X.rk_bot] at this
      exact absurd h (Nat.cast_ne_zero.2 this.ne')

/-- The rank-weighted mean of `μ(N ω) − h ω` over the words of a frame. -/
noncomputable def Frame.mean (F : Frame) : ℝ :=
  (∑ ω, ((F.N ω).deg ⊤ - F.h ω * (F.N ω).rk ⊤)) / ∑ ω, ((F.N ω).rk ⊤ : ℝ)

end SlopeFrame

namespace ZetaBalance

open SlopeFrame

namespace Setting

variable (S : Setting)

/-- `log Ω = γ + log(π/v) − Re L′/L(1, χ_d)`, at a scale `v`. -/
noncomputable def logΩ (v : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi / v) - (logDeriv (LFunction (legChar S.d)) 1).re

/-- `Λ = Σ_{j<m} |Φ|⁻¹ Σ_ρ log(w_j(ρ)·v/π) + m·lg`, for weights `w_j`: the size that the auxiliary primes must
reach. -/
noncomputable def lam {m : ℕ} (w : Fin m → Φ S.A → ℝ) (v lg : ℝ) : ℝ :=
  ∑ j, (Fintype.card (Φ S.A) : ℝ)⁻¹ * ∑ ρ, Real.log (w j ρ * v / Real.pi) + m * lg

/-- `MAIN_ω = Σ_t [m(φ(a_t) − a_t log Ω) − a_t log T]`, with `φ(y) = y log y − y`: the main term of a word whose
auxiliary prime is `T`. -/
noncomputable def mainW (TT : Finset S.A) (m : ℕ) (a : S.A → ℝ) (v T : ℝ) : ℝ :=
  ∑ t ∈ TT, (m * (a t * Real.log (a t) - a t - a t * S.logΩ v) - a t * Real.log T)

/-- **The key identity**: `Σ_t m(φ(a_t) − a_t log Ω) − (Σ_t a_t)·Λ + m(Σ_t a_t)·lg = Σ_t Σ_j MAIN(a_t, w_j)`. The
terms in `log(π/v)` cancel. -/
theorem key_identity (TT : Finset S.A) {m : ℕ} (a : S.A → ℝ) (w : Fin m → Φ S.A → ℝ) (hw : ∀ j ρ, 0 < w j ρ)
    {v : ℝ} (hv : 0 < v) (lg : ℝ) :
    ∑ t ∈ TT, m * (a t * Real.log (a t) - a t - a t * S.logΩ v) - (∑ t ∈ TT, a t) * S.lam w v lg +
      m * (∑ t ∈ TT, a t) * lg = ∑ t ∈ TT, ∑ j, S.MAIN (a t) (w j) := by
  have hΦ : (Fintype.card (Φ S.A) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- `Λ = Σ_j |Φ|⁻¹ Σ_ρ log w_j(ρ) + m(log v − log π) + m·lg`
  have hlam : S.lam w v lg = ∑ j, (Fintype.card (Φ S.A) : ℝ)⁻¹ * ∑ ρ, Real.log (w j ρ) +
      m * (Real.log v - Real.log Real.pi) + m * lg := by
    have e (j : Fin m) (ρ : Φ S.A) :
        Real.log (w j ρ * v / Real.pi) = Real.log (w j ρ) + (Real.log v - Real.log Real.pi) := by
      rw [Real.log_div (mul_pos (hw j ρ) hv).ne' Real.pi_ne_zero, Real.log_mul (hw j ρ).ne' hv.ne', add_sub_assoc]
    simp only [lam, e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_add, ← mul_assoc, inv_mul_cancel₀ hΦ, one_mul]
  -- the identity at each `t`
  have ht (b : ℝ) : m * (b * Real.log b - b - b * S.logΩ v) - b * S.lam w v lg + m * b * lg =
      ∑ j, S.MAIN b (w j) := by
    simp only [MAIN, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, hlam, logΩ, Real.log_div Real.pi_ne_zero hv.ne']
    ring
  rw [← Finset.sum_congr rfl fun t (_ : t ∈ TT) => ht (a t)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]

end Setting

/-- **Six-term data at `x`**: weights for the kernel `A₀` of `κ` and, at each translate `u ∈ A₀`, a frame with a loss
`L_u` bounding its rank-weighted mean slope less the slope of its target (the frame inequality's conclusion), with the
numbers of its words and of the translate that meet the six inequalities G1–G6, and one budget (Z′) for every slack
and the frame losses. -/
structure SixTermData (S : Setting) (κ : S.A →* ℂˣ) (x ε X : ℝ) extends Weights S κ x ε X where
  /-- The frame at each translate: words `ω` with sources `N_ω`, mapping to the target `C_u` with heights `h_ω`. -/
  frame : S.A → Frame
  /-- The frame losses `L_u`. -/
  L : S.A → ℝ
  /-- The slope `μ(M_ω)` of the lattice of forms of each word. -/
  μM : ∀ u, (frame u).ι → ℝ
  /-- The split primes `Ee_ω` of each word. -/
  Ee : ∀ u, (frame u).ι → ℝ
  /-- The auxiliary prime `T_ω` of each word; only `log T_ω` enters. -/
  T : ∀ u, (frame u).ι → ℝ
  /-- The vanishing gain `Ga_u` at the inert places. -/
  Ga : S.A → ℝ
  /-- The forced vanishing `Fo_u`. -/
  Fo : S.A → ℝ
  /-- The scale `v_u` of `log Ω` and `Λ_u`. -/
  v : S.A → ℝ
  /-- `lg_u = log(g₀g₁)`. -/
  lg : S.A → ℝ
  /-- The slack of G1, which bounds the losses `Lo_ω` of the words. -/
  c₁ : S.A → ℝ
  /-- The slack of G2. -/
  c₂ : S.A → ℝ
  /-- The slack of G3. -/
  c₃ : S.A → ℝ
  /-- The slack of G4. -/
  c₄ : S.A → ℝ
  /-- The slack of G5. -/
  c₅ : S.A → ℝ
  /-- The slack of G6. -/
  c₆ : S.A → ℝ
  /-- The ranks of the words add up to a positive number. -/
  rk_pos : ∀ u ∈ A₀ κ, 0 < ∑ ω, (((frame u).N ω).rk ⊤ : ℝ)
  /-- **The frame loss**: `s_u − μ(C_u) ≤ L_u` at the rank-weighted mean slope `s_u`, the conclusion of the frame
  inequality (`Frame.Spread.frame_le`). -/
  frame_le : ∀ u ∈ A₀ κ, (frame u).mean - (frame u).C.deg ⊤ / (frame u).C.rk ⊤ ≤ L u
  /-- The scale is positive. -/
  v_pos : ∀ u ∈ A₀ κ, 0 < v u
  /-- **G1**, the vanishing: `μ(N_ω) ≥ μ(M_ω) + Ga + Fo − Ee_ω − c₁`. -/
  G1 : ∀ u ∈ A₀ κ, ∀ ω, μM u ω + Ga u + Fo u - Ee u ω - c₁ u ≤ ((frame u).N ω).deg ⊤ / ((frame u).N ω).rk ⊤
  /-- **G2**, the forms: `μ(M_ω) ≥ −c₂`. -/
  G2 : ∀ u ∈ A₀ κ, ∀ ω, -c₂ u ≤ μM u ω
  /-- **G3**, the target: `μ(C_u) + h_ω − Fo ≤ MAIN_ω + c₃`. -/
  G3 : ∀ u ∈ A₀ κ, ∀ ω, (frame u).C.deg ⊤ / (frame u).C.rk ⊤ + (frame u).h ω - Fo u ≤
    S.mainW TT m a (v u) (T u ω) + c₃ u
  /-- **G4**, the auxiliary primes: `Λ_u − c₄ ≤ log T_ω`. -/
  G4 : ∀ u ∈ A₀ κ, ∀ ω, S.lam (w u) (v u) (lg u) - c₄ u ≤ Real.log (T u ω)
  /-- **G5**, the split primes: `Ee_ω − m(Σ_t a_t)·lg ≤ c₅`. -/
  G5 : ∀ u ∈ A₀ κ, ∀ ω, Ee u ω - m * (∑ t ∈ TT, a t) * lg u ≤ c₅ u
  /-- **G6**, the gain: `Σ_t Σ_j ASK(a_t, t, w_{u,j}) − Ga ≤ c₆`. -/
  G6 : ∀ u ∈ A₀ κ, ∑ t ∈ TT, ∑ j, S.ASK (a t) t (w u j) - Ga u ≤ c₆ u
  /-- **(Z′)**: the slacks and the frame losses are small. -/
  sizes : ∑ u ∈ A₀ κ, (c₁ u + c₂ u + c₃ u + (∑ t ∈ TT, a t) * c₄ u + c₅ u + c₆ u + L u) ≤
    (A₀ κ).card * x ^ (4 * ε) * ∑ t ∈ TT, a t

namespace SixTermData

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (D : SixTermData S κ x ε X)

/-- The slack of a translate, `c_u = c₁ + c₂ + c₃ + (Σ_t a_t)·c₄ + c₅ + c₆`. -/
noncomputable def slack (u : S.A) : ℝ :=
  D.c₁ u + D.c₂ u + D.c₃ u + (∑ t ∈ D.TT, D.a t) * D.c₄ u + D.c₅ u + D.c₆ u

/-- **(G) at one word**: `μ(N_ω) − h_ω − μ(C_u) ≥ gap(u) − c_u`. `Fo` cancels between G1 and G3, `log T_ω` between
G3 and G4, and `lg` between G4 and G5; the key identity turns what is left into the gap. -/
theorem gap_le_word {u : S.A} (hu : u ∈ A₀ κ) (ω : (D.frame u).ι) :
    S.gap D.TT D.m D.a D.w u - D.slack u ≤
      ((D.frame u).N ω).deg ⊤ / ((D.frame u).N ω).rk ⊤ - (D.frame u).h ω -
        (D.frame u).C.deg ⊤ / (D.frame u).C.rk ⊤ := by
  have key := S.key_identity D.TT D.a (D.w u) (D.w_pos u) (D.v_pos u hu) (D.lg u)
  have h3 := D.G3 u hu ω
  rw [Setting.mainW, Finset.sum_sub_distrib, ← Finset.sum_mul] at h3
  have h4 := mul_le_mul_of_nonneg_left (D.G4 u hu ω) (Finset.sum_nonneg fun t ht => (D.a_pos t ht).le)
  simp only [Setting.gap, Finset.sum_sub_distrib, slack]
  linarith [D.G1 u hu ω, D.G2 u hu ω, D.G5 u hu ω, D.G6 u hu]

/-- **(G) at one translate**: `s_u − μ(C_u) ≥ gap(u) − c_u`, with `s_u` the rank-weighted mean of `μ(N_ω) − h_ω`. -/
theorem gap_le_mean {u : S.A} (hu : u ∈ A₀ κ) :
    S.gap D.TT D.m D.a D.w u - D.slack u ≤ (D.frame u).mean - (D.frame u).C.deg ⊤ / (D.frame u).C.rk ⊤ := by
  rw [Frame.mean, le_sub_iff_add_le, le_div_iff₀ (D.rk_pos u hu), Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h := mul_le_mul_of_nonneg_right (D.gap_le_word hu ω) (Nat.cast_nonneg (((D.frame u).N ω).rk ⊤))
  linarith [((D.frame u).N ω).slope_mul_rk]

/-- **Six-term data are lattice data**, with `s_u` the rank-weighted mean of `μ(N_ω) − h_ω`, the same losses `L_u`
and `E = Σ_{u ∈ A₀} c_u`. -/
noncomputable def toLatticeData : LatticeData S κ x ε X where
  toWeights := D.toWeights
  frame := D.frame
  s u := (D.frame u).mean
  L := D.L
  E := ∑ u ∈ A₀ κ, D.slack u
  frame_le := D.frame_le
  gain := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun u hu => by linarith [D.gap_le_mean hu]
  sizes := by
    rw [← Finset.sum_add_distrib]
    exact D.sizes

end SixTermData

/-- **The six-term frontier for every primitive character**: `PairBound` with six-term data in place of lattice data.
For every primitive `χ`, at arbitrarily small `ε` there is `A ≥ 1` such that, for every large `Y`, every pair `(q, d)`
meeting `ZetaTwist.WinPair ε Y` has a sub-window `[Y′, Y′²]`, with `Y ≤ Y′ ≤ Y^{A/2}`, at each `x` of which a setting
with that pair and a character `κ` of `A` lifting `χ` has six-term data whose thin classes lie beyond `(Nx)^{log x}`.
Like `PairBound`, frames of rank one satisfy it whenever the averaged gap bound holds. -/
def SixTermBound : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧
    ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.Lifts κ χ ∧ Nonempty (SixTermData S κ x ε (((S.N : ℝ) * x) ^ Real.log x))

/-- **CONDITIONAL. The Riemann hypothesis for `ζ` and every Dirichlet `L`-function from the six-term frontier**
(conditional on the half-plane `Re s > 11/12`, through `rhAndGRH_of_pairBound`). -/
theorem rhAndGRH_of_sixTermBound (h : SixTermBound) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_pairBound fun f _ χ hχ ε₀ hε₀ => by
    obtain ⟨ε, hε, hεε₀, A, hA, hY⟩ := h f χ hχ ε₀ hε₀
    refine ⟨ε, hε, hεε₀, A, hA, hY.mono fun Y hY q d hp => ?_⟩
    obtain ⟨Y', hY', hx⟩ := hY q d hp
    refine ⟨Y', hY', fun x hx' => ?_⟩
    obtain ⟨S, κ, hq, hd, hL, hD⟩ := hx x hx'
    exact ⟨S, κ, hq, hd, hL, hD.map SixTermData.toLatticeData⟩

end ZetaBalance

#print axioms ZetaBalance.rhAndGRH_of_sixTermBound
