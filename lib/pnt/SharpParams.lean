import SharpAdm
import DesignTops

/-!
# The design's parameters

A step of the proof of the sharp frontier (`SharpInputs`): the field `SharpPieces.params`, from `ShortNorm`
(`sharpParams`, design spec §4.1). For a primitive `χ` mod `f` and `ε₀ > 0`: `ε = min(ε₀, 1/52)/2`, `A = 2`, and for
`Y` large and a pair `(q, d)` of `ZetaTwist.WinPair ε Y`, the window `Y′ = Y`; at every `x ∈ [Y, Y²]`, the setting of
the pair (`pairSetting`, with `κ = pairChar` lifting `χ`) at a level `e` with `x^{2+8ε} ≤ 2^e ≤ 2x^{2+8ε}`
(`exists_level`) carries an admissible design (`SharpDesign.Adm`, `SharpAdm`).

**The builder** (`buildDesign`, `buildDesign_adm`). From the setting-level clauses (`Setting.DesignAdm`), tops `TT`,
parameters (`DesignPar`) and split primes meeting `BuildOk`: the design with the ranks `designRanks`, the families
`designFam` with weights `w_{u,j} = e_j` and twisted tops (the data `(a_t, b_t)` of the translate `t` at the place
`(1, c·t)`, `c = twA κ`: `SharpAdm`, "Why twisted tops"), the scales `a_t`, the thick set `{a₀^s : s ∈ T}` and
`δ = 2mH + 1 + b/(kx^{13})`. Its `Weights` fields: `thick_near` from the windows of `DesignHC` and
`a_t/x ∈ [b, b + b/(kx^{13})]`; `thick_small` and `thin_far` from the sizes of `SharpAdm`, with
`X = (Nx)^{log x} ≤ X′/3` (`X_le`; a top, at `(1, c·t)`, is thin to `Weights`); `thick_card` as `s ↦ a₀^s` is injective
on `T`; `shares` from exact coset counts (`shares_of_counts`). Every clause of `Adm` is then a hypothesis, a definition
or a lemma (`counts_archive`, `margin`). The builder takes `TT`, the scales and the top shifts as inputs, so the Stage-2
random choices change only its inputs.

**The inputs** (`exists_design`): tops with exact coset counts and `M = ⌈δ₁|A|/(3o + 1)⌉` (`exists_tops`,
`exists_TT_counts`); a generator of the cyclic `A₀` and a relation-free `T` of Behrend type, dense by Behrend's
comparison (`exists_thick`, `RelFree.exists_six`, `eventually_behrend`); `a_t = ⌈a⌉`, `b_t = ⌈b′⌉`; `s* ∈ T`; the
shifts of `exists_shift_RU`; the split primes as a hypothesis.

**The setting** (`pairSetting_designAdm`). `WinPair` gives `d ≡ 7 (mod 16)`, `q ≡ 3 (mod 8)`,
`log q, log d > Y^{ε/5}/2 ≥ x^{ε/10}/2`, `(−d/p) = 1` for `q` and every prime `p ≤ x^{ε/10}` (they divide `d + 1`,
`jacobiSym_neg_eq_one`) and `log N ≤ 4 log x + x^{ε/5} + x^{ε/5}log² x ≤ 3x^{ε/5}log² x`; `PairSetting` gives the
window of `|A|` (`2^e ≤ |A| = o|A₀| ≤ o·2^e`) and `QS ≤ 4·2^e·f`; Littlewood's bound
`|L′/L(1, χ_d)| ≤ M log log(d + 16)` (`Littlewood.norm_logDeriv_one_le`, unconditional) gives A4.

**The thresholds** of `sharpParams`, all at `x ≥ Y`: the growth package, `ord χ, f ≤ x^{ε/100}`, `8f ≤ x`,
`log x ≥ 4`, `M log x ≤ x^ε`, Behrend's comparison at `C = 6` and `ShortNorm`'s `x₀` (`exists_split_primes`); and
`f ≤ Y^{ε/5}/2` for `PairArith`.

**Inputs.** `ShortNorm`, for the split primes only. The primitivity of `χ` is not used: the field's shape asks for
it.
-/

open NumberField Filter

namespace ZetaBalance

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε : ℝ}

/-! ## The builder -/

/-- The design's ranks, `designRanks` at `x` (`Setting.DesignAdm` carries their hypotheses). -/
noncomputable abbrev Setting.DesignAdm.R (hS : S.DesignAdm κ x ε) : S.Ranks :=
  designRanks S x ε hS.big hS.card_ge hS.card_le

/-- The thick set `T2 = {a₀^s : s ∈ T}` of the parameters. -/
noncomputable abbrev DesignPar.T2 (pr : DesignPar S) : Finset S.A := pr.T.image (pr.a₀ ^ ·)

/-- **What the builder needs of its inputs**: exact coset counts of the tops (`exists_TT_counts`) and their density
window, the windows of `a_t` and `b_t`, a generator `a₀` of `A₀`, a relation-free dense `T` in range with `s* ∈ T`,
shifts `σ < w_E` meeting the root-of-unity condition, and split primes. -/
structure BuildOk (hS : S.DesignAdm κ x ε) (TT : Finset S.A) (pr : DesignPar S) (g₀ g₁ : ℕ) : Prop where
  /-- Exact counts: `4M` tops in `A₀` and `3M` over each other value of `κ`, `M > 0`. -/
  counts : ∃ M, 0 < M ∧ ∀ ζ : ℂˣ,
    (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0
  /-- `|TT| ≥ δ₁|A|/2`. -/
  TT_ge : scδ₁ x ε * Fintype.card S.A / 2 ≤ TT.card
  /-- `|TT| ≤ 2δ₁|A|`. -/
  TT_le : (TT.card : ℝ) ≤ 2 * scδ₁ x ε * Fintype.card S.A
  /-- `a ≤ a_t ≤ a + a/(kx^{13})`. -/
  a_mem : ∀ t ∈ TT, scA x ε ≤ pr.aZ t ∧ (pr.aZ t : ℝ) ≤ scA x ε + scA x ε / (designK x ε * x ^ 13)
  /-- `b′ ≤ b_t ≤ b′(1 + x^{−1/4})`. -/
  bT_mem : ∀ t ∈ TT, scB' x ε ≤ pr.bT t ∧ (pr.bT t : ℝ) ≤ scB' x ε * (1 + x ^ (-(1 / 4 : ℝ)))
  /-- `a₀ ∈ A₀`. -/
  a₀_mem : pr.a₀ ∈ A₀ κ
  /-- `a₀` has order `|A₀|`. -/
  a₀_order : orderOf pr.a₀ = (A₀ κ).card
  /-- `4L_w s < |A₀|` on `T`. -/
  T_range : ∀ s ∈ pr.T, 4 * scLw x ε * s < (A₀ κ).card
  /-- `T` is relation-free at level `L_w`. -/
  T_relFree : RelFree pr.T (scLw x ε)
  /-- `|T| ≥ x^{−ε}|A|`. -/
  T_card : x ^ (-ε) * Fintype.card S.A ≤ pr.T.card
  /-- `s* ∈ T`. -/
  sstar_mem : pr.sstar ∈ pr.T
  /-- `σ(u) < w_E`. -/
  σ_lt : ∀ u, pr.σ u < Units.torsionOrder S.E
  /-- The root-of-unity condition for the families (twisted tops: the data of `t` at `(1, c·t)`, `c = twA κ`). -/
  ru : ∀ hyp : DesignHyp S x ε hS.R (TT.image (S.twA κ * ·)) (pr.aZ ∘ (S.twA κ * ·)) (pr.bT ∘ (S.twA κ * ·)),
    ∀ u j (ζ : S.E), (∃ n, 0 < n ∧ ζ ^ n = 1) →
      ∏ ρ, (S.τ ρ ζ) ^ ((designFam S x ε hS.R (TT.image (S.twA κ * ·)) pr.T2 (pr.aZ ∘ (S.twA κ * ·))
        (pr.bT ∘ (S.twA κ * ·)) (designStar pr.a₀ pr.sstar) pr.σ hyp u ρ).e j) = 1
  /-- `g₀` is prime. -/
  g₀_prime : g₀.Prime
  /-- `g₁` is prime. -/
  g₁_prime : g₁.Prime
  /-- `g₀ ≠ g₁`. -/
  g₀_ne_g₁ : g₀ ≠ g₁
  /-- The split primes are large, of norm one modulo `N`. -/
  split : ∀ g ∈ [g₀, g₁], ((designK x ε : ℝ) * scB x ε) ^ 8 ≤ g ∧ (g : ℝ) ≤ 2 * ((designK x ε : ℝ) * scB x ε) ^ 8 ∧
    ∃ α β : ℤ, 4 * (g : ℤ) = α ^ 2 + S.d * β ^ 2 ∧ (S.N : ℤ) ∣ β ∧ α ≡ β + 2 [ZMOD 2 * S.N]
  /-- Their exceptional sets are disjoint. -/
  exc : Disjoint (ExcSet (designK x ε + designM x ε - 1) g₀) (ExcSet (designK x ε + designM x ε - 1) g₁)

namespace Setting.DesignAdm

variable (hS : S.DesignAdm κ x ε)
include hS

/-- `k + 5 < 2⌊b′/x⌋`, as `b′/x = b/X′ ≥ x^{440}` and `k ≤ 2x^5`: the margin `P > (k − 1)/2 + 3`. -/
theorem margin : (designK x ε : ℤ) + 5 < 2 * ⌊scB' x ε / x⌋ := by
  have hx := hS.big.x_ge
  have hk := hS.big.designK_le.2
  have hb : x ^ 440 ≤ scB' x ε / x := by
    rw [scB'_eq, mul_div_cancel_left₀ _ hS.big.pos.ne']
    exact hS.big.bX'_ge
  have hfl := Int.sub_one_lt_floor (scB' x ε / x)
  have h1 : x ^ 5 * x ≤ x ^ 440 := by rw [← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have h2 : 1 ≤ x ^ 5 := one_le_pow₀ (by linarith)
  have : ((designK x ε : ℤ) + 5 : ℝ) < 2 * (⌊scB' x ε / x⌋ : ℝ) := by push_cast; nlinarith
  exact_mod_cast this

/-- **The inequalities of the families** (`HCHyp`) at the design's integers, for scales `a_t ≥ a` and top shifts
`b_t ≥ b′`: `Δ ≥ 1`, `2H ≥ x^{402} ≥ t + 3`, `B, W ≥ 1`, `2P ≥ k` (`margin`), `a_t ≥ xb ≥ 16x^6 ≥ 4Δk`. -/
theorem buildHyp {TT : Finset S.A} {aZ bT : S.A → ℤ} (ha : ∀ t ∈ TT, scA x ε ≤ aZ t)
    (hb : ∀ t ∈ TT, scB' x ε ≤ bT t) : DesignHyp S x ε hS.R TT aZ bT where
  Δ_pos := hS.big.designΔ_mem.1
  H_ge := by
    have ht := designT_le S hS.big hS.card_le
    have hH := hS.designH_mem.2.1
    have hx := hS.big.x_ge
    have h1 : x ^ 401 * x ≤ x ^ 402 := by rw [← pow_succ]
    have h2 : 1 ≤ x ^ 401 := one_le_pow₀ (by linarith)
    have : (designT S x ε : ℝ) + 3 ≤ 2 * designH S x := by nlinarith
    show designT S x ε + 3 ≤ 2 * designH S x
    exact_mod_cast this
  B_pos := by have := Int.ceil_pos.2 (Real.exp_pos (scL x ε)); unfold scB; omega
  W_pos := by have := Int.ceil_pos.2 (scW''_pos S ε hS.big.pos); omega
  P_gt := by have := hS.margin; show (designK x ε : ℤ) ≤ _; omega
  a_ge t ht := by
    have hx := hS.big.x_ge
    obtain ⟨hΔ1, hΔ2⟩ := hS.big.designΔ_mem
    have hk := hS.big.designK_le.2
    have hb := hS.big.b_ge'
    have h1 : x ^ 6 * 16 ≤ x ^ 6 * x ^ 844 :=
      mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))) (by positivity)
    have h2 : (designΔ x : ℝ) * designK x ε ≤ (2 * x) * (2 * x ^ 5) := mul_le_mul hΔ2 hk (by positivity) (by linarith)
    have h3 : 4 * (designΔ x : ℝ) * designK x ε ≤ scA x ε := by
      unfold scA
      nlinarith [pow_pos hS.big.pos 6]
    have : (4 * (designΔ x : ℤ) * designK x ε : ℝ) ≤ aZ t := by push_cast; linarith [ha t ht]
    exact_mod_cast this
  bT_nonneg t ht := by
    have := lt_of_lt_of_le (scB'_pos ε hS.big.pos) (hb t ht)
    exact_mod_cast this.le

/-- `X = (Nx)^{log x} ≤ X′/3`: `log X = log x·(log N + log x) ≤ 3x^{ε/5}log³ x + log² x ≤ x^{ε/3} − 2`. -/
theorem X_le : ((S.N : ℝ) * x) ^ Real.log x ≤ scX' x ε / 3 := by
  have hx0 := hS.big.pos
  have hl := hS.big.one_le_log
  have hN0 : (0 : ℝ) < S.N := Nat.cast_pos.2 (NeZero.pos _)
  have hlN := hS.log_N_le
  have hth := hS.big.thin
  have hlNx : Real.log ((S.N : ℝ) * x) * Real.log x ≤ x ^ (ε / 3) - 2 := by
    rw [Real.log_mul hN0.ne' hx0.ne']
    have h0 : 0 ≤ Real.log x := by linarith
    calc (Real.log S.N + Real.log x) * Real.log x ≤ (3 * x ^ (ε / 5) * Real.log x ^ 2 + Real.log x) * Real.log x := by
          gcongr
      _ = 3 * x ^ (ε / 5) * Real.log x ^ 3 + Real.log x ^ 2 := by ring
      _ ≤ x ^ (ε / 3) - 2 := by linarith
  have he2 : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [Real.rpow_def_of_pos (mul_pos hN0 hx0)]
  calc Real.exp (Real.log ((S.N : ℝ) * x) * Real.log x) ≤ Real.exp (x ^ (ε / 3) - 2) := Real.exp_le_exp.2 hlNx
    _ = scX' x ε / Real.exp 2 := by rw [Real.exp_sub]; rfl
    _ ≤ scX' x ε / 3 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) he2

end Setting.DesignAdm

namespace BuildOk

variable {hS : S.DesignAdm κ x ε} {TT : Finset S.A} {pr : DesignPar S} {g₀ g₁ : ℕ} (hI : BuildOk hS TT pr g₀ g₁)
include hI

/-- The inequalities of the builder's families, with twisted tops: the tops `c·TT` carry `a_{c·y}`, `b_{c·y}`. -/
theorem hyp : DesignHyp S x ε hS.R (TT.image (S.twA κ * ·)) (pr.aZ ∘ (S.twA κ * ·)) (pr.bT ∘ (S.twA κ * ·)) :=
  hS.buildHyp (fun _ hy => (hI.a_mem _ (S.twA_mul_mem_of_mem_image κ hy)).1)
    (fun _ hy => (hI.bT_mem _ (S.twA_mul_mem_of_mem_image κ hy)).1)

/-- **The builder's families**: `designFam` at the parameters, with **twisted tops**: the top data `(a_t, b_t)` of
the translate `t` sits at the place `(1, c·t)`, `c = twA κ`. -/
noncomputable abbrev fam : S.A → hS.R.HCFamily :=
  designFam S x ε hS.R (TT.image (S.twA κ * ·)) pr.T2 (pr.aZ ∘ (S.twA κ * ·)) (pr.bT ∘ (S.twA κ * ·))
    (designStar pr.a₀ pr.sstar) pr.σ hI.hyp

/-- `b′ ≤ b_t ≤ 2b′`. -/
theorem bT_le : ∀ t ∈ TT, scB' x ε ≤ pr.bT t ∧ (pr.bT t : ℝ) ≤ 2 * scB' x ε := fun t ht =>
  ⟨(hI.bT_mem t ht).1, hS.big.le_two_mul_scB' (hI.bT_mem t ht).2⟩

/-- `b′ ≤ b_{c·y} ≤ 2b′` at the twisted tops `y ∈ c·TT`. -/
theorem bT_le_tw : ∀ y ∈ TT.image (S.twA κ * ·), scB' x ε ≤ pr.bT (S.twA κ * y) ∧
    (pr.bT (S.twA κ * y) : ℝ) ≤ 2 * scB' x ε := fun _ hy =>
  hI.bT_le _ (S.twA_mul_mem_of_mem_image κ hy)

/-- **`Weights.thick_near`**: a thick weight lies in `[b, b + 2mH + 1]` (`hcFam_windows`) and
`a_t/x ∈ [b, b + b/(kx^{13})]`. -/
theorem thick_near {t : S.A} (ht : t ∈ TT) (u : S.A) (j : Fin hS.R.m) {s : S.A} (hs : s ∈ pr.T2) :
    |((hI.fam u (-1, s * u)).e j : ℝ) - (pr.aZ t : ℝ) / x| ≤
      hS.R.m * (2 * designH S x) + 1 + scB x ε / (hS.R.k * x ^ 13) := by
  have hpk : placeKind (TT.image (S.twA κ * ·)) pr.T2 u (-1, s * u) = .thick :=
    placeKind_eq_thick.2 (Finset.mem_image_of_mem _ hs)
  have hσH : ∀ u, pr.σ u ≤ designH S x := fun u => by
    have h1 : (pr.σ u : ℝ) < designH S x := lt_of_lt_of_le (by exact_mod_cast hI.σ_lt u) hS.designH_mem.1
    exact_mod_cast h1.le
  obtain ⟨e1, e2⟩ := (hcFam_windows hI.hyp (T2 := pr.T2) (ρstar := designStar pr.a₀ pr.sstar) (bR := scB x ε)
    (wR := scW'' S x ε) (pR := scB' x ε / x) rfl rfl rfl hσH u (-1, s * u) j).2.1 hpk
  have e1' : scB x ε ≤ ((hI.fam u (-1, s * u)).e j : ℝ) := e1
  have e2' : ((hI.fam u (-1, s * u)).e j : ℝ) ≤ scB x ε + (designM x ε : ℝ) * (2 * designH S x) + 1 := e2
  obtain ⟨a1, a2⟩ := hI.a_mem t ht
  have hx0 := hS.big.pos
  have hk1 := hS.big.designK_le.1
  have hd : 0 ≤ scB x ε / (designK x ε * x ^ 13) := div_nonneg (Real.exp_pos _).le (by positivity)
  have hA1 : scB x ε ≤ (pr.aZ t : ℝ) / x := by
    rw [le_div_iff₀ hx0]
    unfold scA at a1
    linarith
  have hA2 : (pr.aZ t : ℝ) / x ≤ scB x ε + scB x ε / (designK x ε * x ^ 13) := by
    have e : x * (scB x ε + scB x ε / (designK x ε * x ^ 13)) = scA x ε + scA x ε / (designK x ε * x ^ 13) := by
      unfold scA
      ring
    rw [div_le_iff₀ hx0, mul_comm]
    linarith
  have hη : 0 ≤ (designM x ε : ℝ) * (2 * designH S x) := by positivity
  show _ ≤ (designM x ε : ℝ) * (2 * designH S x) + 1 + scB x ε / (designK x ε * x ^ 13)
  rw [abs_le]
  constructor <;> linarith

/-- **`Weights.thick_small`**: `64|A|x³δ ≤ a_t`, as `64|A|x³(2mH + 1) ≤ 64x^{416} ≤ xb/2` and
`64|A|x³·b/(kx^{13}) ≤ 64b/x^7 ≤ xb/2`. -/
theorem thick_small {t : S.A} (ht : t ∈ TT) :
    64 * Fintype.card S.A * x ^ 3 * (hS.R.m * (2 * designH S x) + 1 + scB x ε / (hS.R.k * x ^ 13)) ≤
      pr.aZ t := by
  have hx := hS.big.x_ge
  have hx0 := hS.big.pos
  have hη := hS.eta_le (m := designM x ε) hS.big.designM_le
  have hn := hS.card_le_cube
  have hn0 : (0 : ℝ) ≤ Fintype.card S.A := Nat.cast_nonneg _
  have hk1 := hS.big.designK_le.1
  have hb := hS.big.b_ge'
  have h13 : 0 < x ^ 13 := pow_pos hx0 13
  set B := scB x ε / x ^ 13 with hB
  have hB0 : 0 ≤ B := div_nonneg (Real.exp_pos _).le h13.le
  have hbB : scB x ε = x ^ 13 * B := by rw [hB, mul_div_cancel₀ _ h13.ne']
  have hdiv : scB x ε / (designK x ε * x ^ 13) ≤ B :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le h13 (by nlinarith)
  have hd0 : 0 ≤ scB x ε / (designK x ε * x ^ 13) := div_nonneg (Real.exp_pos _).le (by positivity)
  have h1 : 64 * (Fintype.card S.A : ℝ) * x ^ 3 * ((designM x ε : ℝ) * (2 * designH S x) + 1) ≤
      64 * x ^ 416 := by
    calc _ ≤ 64 * x ^ 3 * x ^ 3 * x ^ 410 := by gcongr
      _ = 64 * x ^ 416 := by ring
  have h2 : 64 * (Fintype.card S.A : ℝ) * x ^ 3 * (scB x ε / (designK x ε * x ^ 13)) ≤ 64 * x ^ 6 * B := by
    calc _ ≤ 64 * x ^ 3 * x ^ 3 * B := by gcongr
      _ = 64 * x ^ 6 * B := by ring
  have h3 : 64 * x ^ 416 ≤ x * scB x ε / 2 := by
    have : x ^ 416 * 128 ≤ x ^ 416 * x ^ 435 :=
      mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))) (by positivity)
    nlinarith [pow_pos hx0 416]
  have h4 : 64 * x ^ 6 * B ≤ x * scB x ε / 2 := by
    have : x ^ 6 * 128 ≤ x ^ 6 * x ^ 8 :=
      mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))) (by positivity)
    rw [hbB]
    nlinarith [mul_le_mul_of_nonneg_right this hB0]
  have h5 := (hI.a_mem t ht).1
  show 64 * (Fintype.card S.A : ℝ) * x ^ 3 *
    ((designM x ε : ℝ) * (2 * designH S x) + 1 + scB x ε / (designK x ε * x ^ 13)) ≤ pr.aZ t
  unfold scA at h5
  nlinarith

/-- **`Weights.thin_far`**: `X ≤ X′/3 ≤ a_t/w` off the thick classes: at a top `w ≤ 3b′` and `a/(3b′) = X′/3`; at a
thin place `w ≤ 2w″` and `a/(2w″) = x|A|X′/2` (`e_window`, `X_le`). -/
theorem thin_far {t : S.A} (ht : t ∈ TT) (u : S.A) (j : Fin hS.R.m) {ρ : Φ S.A} (hρ : ρ ∉ S.thickSet pr.T2 u) :
    ((S.N : ℝ) * x) ^ Real.log x ≤ (pr.aZ t : ℝ) / (hI.fam u ρ).e j := by
  obtain ⟨wt, wn, wl, -⟩ := hS.e_window (T2 := pr.T2) (ρstar := designStar pr.a₀ pr.sstar) hS.big.designM_le
    hI.σ_lt hI.bT_le_tw hI.hyp u ρ j
  have hx0 := hS.big.pos
  have hw0 : 0 < scW'' S x ε := scW''_pos S ε hx0
  have he0 : (0 : ℝ) < (hI.fam u ρ).e j := lt_of_lt_of_le hw0 wl
  have hA0 := scA_pos ε hx0
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  have hb0 := scB'_pos ε hx0
  suffices h : scX' x ε / 3 ≤ scA x ε / (hI.fam u ρ).e j from
    hS.X_le.trans (h.trans (div_le_div_of_nonneg_right (hI.a_mem t ht).1 he0.le))
  rcases hpk : placeKind (TT.image (S.twA κ * ·)) pr.T2 u ρ
  · have e : scA x ε / (3 * scB' x ε) = scX' x ε / 3 := by
      unfold scB'
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_left hA0.le he0 (wt hpk)
  · exact absurd (placeKind_eq_thick.1 hpk) hρ
  · have e := scA_div_scW'' S ε hx0
    have hn : (1 : ℝ) ≤ x * Fintype.card S.A := by
      have : (1 : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Fintype.card_pos
      nlinarith [hS.big.x_ge]
    have h1 : scX' x ε / 3 ≤ scA x ε / (2 * scW'' S x ε) := by
      rw [show scA x ε / (2 * scW'' S x ε) = scA x ε / scW'' S x ε / 2 by rw [div_div, mul_comm], e]
      nlinarith
    exact h1.trans (div_le_div_of_nonneg_left hA0.le he0 (wn hpk))

/-- **`Weights.thick_card`**: `|T2| = |T| ≥ x^{−ε}|A| ≥ x^{−ε}|A₀|`, as `s ↦ a₀^s` is injective on `T` (`s < |A₀|`,
the order of `a₀`). -/
theorem thick_card : x ^ (-ε) * (A₀ κ).card ≤ pr.T2.card := by
  have hinj : Set.InjOn (pr.a₀ ^ ·) pr.T := (pow_injOn_Iio_orderOf (x := pr.a₀)).mono fun s hs => by
    have h1 := hI.T_range s hs
    rw [← hI.a₀_order] at h1
    have h2 : s ≤ 4 * scLw x ε * s := Nat.le_mul_of_pos_left s (by unfold scLw; omega)
    exact lt_of_le_of_lt h2 h1
  rw [DesignPar.T2, Finset.card_image_of_injOn hinj]
  have h1 : ((A₀ κ).card : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Finset.card_le_univ _
  have h2 : 0 ≤ x ^ (-ε) := Real.rpow_nonneg hS.big.pos.le _
  calc x ^ (-ε) * (A₀ κ).card ≤ x ^ (-ε) * Fintype.card S.A := by gcongr
    _ ≤ pr.T.card := hI.T_card

/-- **`Weights.shares`** from the exact counts (`shares_of_counts`), with `θ = 1/(kx^{13})`, `2θ ≤ 1/x ≤ x^{ε−1}`. -/
theorem shares : ∀ k, 0 < k → k < orderOf κ → ‖∑ t ∈ TT, ((pr.aZ t : ℝ) : ℂ) * (κ t : ℂ) ^ k -
    (((3 * (orderOf κ : ℝ) + 1)⁻¹ * ∑ t ∈ TT, (pr.aZ t : ℝ) : ℝ) : ℂ)‖ ≤ x ^ (ε - 1) * ∑ t ∈ TT, (pr.aZ t : ℝ) := by
  obtain ⟨M, -, hTT⟩ := hI.counts
  have hx0 := hS.big.pos
  have hx := hS.big.x_ge
  have hk1 := hS.big.designK_le.1
  have h13 : 0 < (designK x ε : ℝ) * x ^ 13 := by positivity
  refine shares_of_counts hTT (a := fun t => (pr.aZ t : ℝ)) (a₀ := scA x ε) (θ := 1 / (designK x ε * x ^ 13))
    (scA_pos ε hx0).le (by positivity) (fun t ht => ⟨(hI.a_mem t ht).1, ?_⟩) ?_
  · have e : scA x ε * (1 + 1 / (designK x ε * x ^ 13)) = scA x ε + scA x ε / (designK x ε * x ^ 13) := by ring
    rw [e]
    exact (hI.a_mem t ht).2
  · have h1 : x ^ (-1 : ℝ) ≤ x ^ (ε - 1) :=
      Real.rpow_le_rpow_of_exponent_le hS.big.one_lt.le (by linarith [hS.big.ε_pos])
    rw [Real.rpow_neg_one] at h1
    have h2 : 2 * (1 / ((designK x ε : ℝ) * x ^ 13)) ≤ x⁻¹ := by
      rw [← one_div, mul_one_div, div_le_div_iff₀ h13 hx0]
      have h3 : x ^ 2 ≤ x ^ 13 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hk1 (pow_pos hx0 13).le]
    linarith

/-- **`Weights.TT_nonempty`**: `|TT| = (3o + 1)M > 0`. -/
theorem TT_nonempty : TT.Nonempty := by
  obtain ⟨M, hM, hTT⟩ := hI.counts
  rw [← Finset.card_pos, card_TT_of_counts hTT]
  positivity

/-- **`(−d/g) = 1`** for the split primes (`jacobiSym_neg_d_of_norm`, with `d ≥ 100` and `d ∣ N ∣ β`). -/
theorem leg {g : ℕ} (hg : g ∈ [g₀, g₁]) (hgp : g.Prime) : jacobiSym (-(S.d : ℤ)) g = 1 := by
  obtain ⟨-, -, α, β, h4, hNβ, -⟩ := hI.split g hg
  exact jacobiSym_neg_d_of_norm h4 hgp (by have := hS.hundred_le_d; omega)
    ((Int.natCast_dvd_natCast.2 S.d_dvd_N).trans hNβ)

end BuildOk

/-- **The builder**: the design at `x` with the given tops `TT`, parameters `pr` and split primes `g₀, g₁`: the
ranks `designRanks`, the weights `w_{u,j} = e_j` of the families `designFam`, the scales `a_t`, the thick set
`{a₀^s : s ∈ T}` and `δ = 2mH + 1 + b/(kx^{13})`. -/
noncomputable def buildDesign (hS : S.DesignAdm κ x ε) (TT : Finset S.A) (pr : DesignPar S) (g₀ g₁ : ℕ)
    (hI : BuildOk hS TT pr g₀ g₁) : SharpDesign S κ x ε (((S.N : ℝ) * x) ^ Real.log x) where
  m := hS.R.m
  TT := TT
  T2 := pr.T2
  a t := pr.aZ t
  w u j ρ := ((hI.fam u ρ).e j : ℝ)
  δ := hS.R.m * (2 * designH S x) + 1 + scB x ε / (hS.R.k * x ^ 13)
  w_pos u j ρ := by
    have := hcFam_e_pos (T2 := pr.T2) (ρstar := designStar pr.a₀ pr.sstar) (σ := pr.σ) hI.hyp u ρ j
    exact_mod_cast this
  a_pos t ht := lt_of_lt_of_le (scA_pos ε hS.big.pos) (hI.a_mem t ht).1
  thick_near t ht u _ j s hs := hI.thick_near ht u j hs
  thick_small t ht := hI.thick_small ht
  thin_far t ht u _ j ρ hρ := hI.thin_far ht u j hρ
  words := le_trans (Real.rpow_le_rpow_of_exponent_le hS.big.one_lt.le (by linarith [hS.big.ε_pos]))
    (designM_mem hS.big).1
  thick_sub s hs := by
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hs
    rw [mem_A₀, map_pow, mem_A₀.1 hI.a₀_mem, one_pow]
  thick_card := hI.thick_card
  shares := hI.shares
  TT_nonempty := hI.TT_nonempty
  R := hS.R
  hm := rfl
  hc := hI.fam
  hw _ _ _ := rfl
  g₀ := g₀
  g₁ := g₁
  g₀_prime := hI.g₀_prime
  g₁_prime := hI.g₁_prime
  g₀_ne_g₁ := hI.g₀_ne_g₁
  leg₀ := hI.leg (by simp) hI.g₀_prime
  leg₁ := hI.leg (by simp) hI.g₁_prime

/-- The built design meets the clauses of its parameters (`SharpDesign.FamAt`). -/
theorem BuildOk.famAt {hS : S.DesignAdm κ x ε} {TT : Finset S.A} {pr : DesignPar S} {g₀ g₁ : ℕ}
    (hI : BuildOk hS TT pr g₀ g₁) : (buildDesign hS TT pr g₀ g₁ hI).FamAt pr where
  a_eq _ := rfl
  a_mem := hI.a_mem
  bT_mem := hI.bT_mem
  a₀_mem := hI.a₀_mem
  a₀_order := hI.a₀_order
  T2_eq := rfl
  T_range := hI.T_range
  T_relFree := hI.T_relFree
  T_card := hI.T_card
  sstar_mem := hI.sstar_mem
  σ_lt := hI.σ_lt
  hyp := hI.hyp
  hc_eq _ := rfl

/-- **The built design is admissible**: every clause is a hypothesis of the builder, a definition (`X`, the ranks,
`T2`, the families) or a lemma (the coset counts from the exact ones, `counts_archive`; the margin). -/
theorem buildDesign_adm (hS : S.DesignAdm κ x ε) (TT : Finset S.A) (pr : DesignPar S) (g₀ g₁ : ℕ)
    (hI : BuildOk hS TT pr g₀ g₁) : (buildDesign hS TT pr g₀ g₁ hI).Adm where
  toDesignAdm := hS
  X_eq := rfl
  k_eq := rfl
  m_eq := rfl
  t_eq := rfl
  TT_ge := hI.TT_ge
  TT_le := hI.TT_le
  TT_counts γ := by
    obtain ⟨M, -, hTT⟩ := hI.counts
    exact counts_archive hTT hS.big.pos.le γ
  P_margin := hS.margin
  fam := ⟨pr, hI.famAt⟩
  ru := hI.ru hI.hyp
  split := hI.split
  exc := hI.exc

/-! ## The inputs of the builder -/

namespace Setting.DesignAdm

variable (hS : S.DesignAdm κ x ε)
include hS

/-- `|A| = o|A₀| ≤ x^{ε/100}|A₀|` and `|A₀| ≥ x^{2+8ε−ε/100} ≥ x`. -/
theorem card_A₀_ge : (Fintype.card S.A : ℝ) ≤ x ^ (ε / 100) * (A₀ κ).card ∧ x ≤ (A₀ κ).card := by
  have hx0 := hS.big.pos
  have h1 : (Fintype.card S.A : ℝ) = orderOf κ * (A₀ κ).card := by exact_mod_cast card_A_eq κ
  have h2 : (Fintype.card S.A : ℝ) ≤ x ^ (ε / 100) * (A₀ κ).card := by
    rw [h1]; gcongr; exact hS.orderOf_le
  refine ⟨h2, ?_⟩
  have h3 : x ^ (2 + 8 * ε) = x ^ (ε / 100) * x ^ (2 + 8 * ε - ε / 100) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have h4 : x ≤ x ^ (2 + 8 * ε - ε / 100) := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hS.big.one_lt.le (by linarith [hS.big.ε_lt, hS.big.ε_pos])
  have h5 := hS.card_ge
  have h6 : 0 < x ^ (ε / 100) := Real.rpow_pos_of_pos hx0 _
  nlinarith

/-- **The tops**: with `M = ⌈δ₁|A|/(3o + 1)⌉ > 0`, `4M ≤ |A₀|`, so `exists_TT_counts` gives tops with exact coset
counts, and `|TT| = (3o + 1)M ∈ [δ₁|A|, δ₁|A| + 3o + 1] ⊆ [δ₁|A|/2, 2δ₁|A|]`. -/
theorem exists_tops : ∃ TT : Finset S.A, (∃ M, 0 < M ∧ ∀ ζ : ℂˣ,
    (TT.filter (κ · = ζ)).card = if ζ = 1 then 4 * M else if ζ ∈ κ.range then 3 * M else 0) ∧
    scδ₁ x ε * Fintype.card S.A / 2 ≤ TT.card ∧ (TT.card : ℝ) ≤ 2 * scδ₁ x ε * Fintype.card S.A := by
  have hx0 := hS.big.pos
  have hx := hS.big.x_ge
  obtain ⟨hA1, hA2⟩ := hS.card_A₀_ge
  have ho1 : (1 : ℝ) ≤ orderOf κ := by exact_mod_cast orderOf_pos κ
  have ho2 := hS.orderOf_le
  have hn : (Fintype.card S.A : ℝ) = orderOf κ * (A₀ κ).card := by exact_mod_cast card_A_eq κ
  have hδ0 : 0 < scδ₁ x ε := Real.rpow_pos_of_pos hx0 _
  have hδ1 : scδ₁ x ε ≤ 1 / 2 := by
    have h1 : 2 ≤ x ^ (ε / 8) := le_trans (by norm_num) (hS.big.le_rpow (by linarith [hS.big.ε_pos]))
    unfold scδ₁
    rw [Real.rpow_neg hx0.le]
    rw [inv_le_comm₀ (Real.rpow_pos_of_pos hx0 _) (by norm_num)]
    linarith
  have h3o : (0 : ℝ) < 3 * orderOf κ + 1 := by positivity
  set c := scδ₁ x ε * Fintype.card S.A / (3 * orderOf κ + 1) with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hM1 : c ≤ ⌈c⌉₊ := Nat.le_ceil c
  have hM2 : (⌈c⌉₊ : ℝ) < c + 1 := Nat.ceil_lt_add_one hc0.le
  have hc3 : c ≤ scδ₁ x ε * (A₀ κ).card / 3 := by
    rw [hc, hn, div_le_div_iff₀ h3o (by norm_num)]
    have : (0 : ℝ) ≤ scδ₁ x ε * (A₀ κ).card := by positivity
    nlinarith
  have h4M : 4 * ⌈c⌉₊ ≤ (A₀ κ).card := by
    have : (4 * ⌈c⌉₊ : ℝ) ≤ (A₀ κ).card := by
      have : scδ₁ x ε * (A₀ κ).card ≤ (A₀ κ).card / 2 := by
        have : (0 : ℝ) ≤ (A₀ κ).card := Nat.cast_nonneg _
        nlinarith
      linarith
    exact_mod_cast this
  obtain ⟨TT, hTT⟩ := exists_TT_counts κ ⌈c⌉₊ h4M
  have hcard : (TT.card : ℝ) = (3 * orderOf κ + 1) * ⌈c⌉₊ := by exact_mod_cast card_TT_of_counts hTT
  have hcc : (3 * orderOf κ + 1) * c = scδ₁ x ε * Fintype.card S.A := by
    rw [hc]; field_simp
  -- `3o + 1 ≤ δ₁|A|`
  have hsmall : 3 * (orderOf κ : ℝ) + 1 ≤ scδ₁ x ε * Fintype.card S.A := by
    have e1 : scδ₁ x ε * x ^ (2 + 8 * ε) = x ^ (ε / 100) * x ^ (2 + 8 * ε - ε / 8 - ε / 100) := by
      unfold scδ₁
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
    have e2 := hS.big.le_rpow (c := 2 + 8 * ε - ε / 8 - ε / 100) (by linarith [hS.big.ε_lt, hS.big.ε_pos])
    have e3 : 1 ≤ x ^ (ε / 100) := Real.one_le_rpow hS.big.one_lt.le (by linarith [hS.big.ε_pos])
    have e4 : scδ₁ x ε * x ^ (2 + 8 * ε) ≤ scδ₁ x ε * Fintype.card S.A :=
      mul_le_mul_of_nonneg_left hS.card_ge hδ0.le
    nlinarith
  refine ⟨TT, ⟨⌈c⌉₊, Nat.ceil_pos.2 hc0, hTT⟩, ?_, ?_⟩
  · rw [hcard]
    have : (3 * orderOf κ + 1 : ℝ) * c ≤ (3 * orderOf κ + 1) * ⌈c⌉₊ := by gcongr
    have : (0 : ℝ) ≤ scδ₁ x ε * Fintype.card S.A := by positivity
    linarith
  · rw [hcard]
    have : (3 * orderOf κ + 1 : ℝ) * ⌈c⌉₊ ≤ (3 * orderOf κ + 1) * (c + 1) := by gcongr
    linarith

/-- **The thick set**: a generator `a₀` of the cyclic `A₀`, and a relation-free `T ⊆ [0, N₀)` at level `L_w`,
`N₀ = ⌊|A₀|/(4L_w)⌋` (`RelFree.exists_six`), so `4L_w s < |A₀|` on `T`. Its density
`N₀e^{−6√(log N₀·log(2L_w + 1))} ≥ |A₀|x^{−ε/2} ≥ |A|x^{−ε}`, from `log N₀ ≤ 3 log x`,
`N₀ ≥ |A₀|/(8L_w)` and Behrend's comparison `8L_w e^{6√(3 log x·log(2L_w + 1))} ≤ x^{ε/2}`. -/
theorem exists_thick [IsCyclic κ.ker]
    (hbeh : 8 * scLw x ε * Real.exp (6 * √(3 * Real.log x * Real.log (2 * scLw x ε + 1))) ≤ x ^ (ε / 2)) :
    ∃ (a₀ : S.A) (T : Finset ℕ), a₀ ∈ A₀ κ ∧ orderOf a₀ = (A₀ κ).card ∧
      (∀ s ∈ T, 4 * scLw x ε * s < (A₀ κ).card) ∧ RelFree T (scLw x ε) ∧
      x ^ (-ε) * Fintype.card S.A ≤ T.card := by
  have hx0 := hS.big.pos
  have hx := hS.big.x_ge
  obtain ⟨hA1, hA2⟩ := hS.card_A₀_ge
  -- the generator
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κ.ker)
  have hord : orderOf (g : S.A) = (A₀ κ).card := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, card_A₀]
  have hgmem : (g : S.A) ∈ A₀ κ := mem_A₀.2 (MonoidHom.mem_ker.1 g.2)
  -- the relation-free set
  set L := scLw x ε with hL
  have hL2 : 2 ≤ L := by unfold scLw at hL; omega
  set c := 6 * √(3 * Real.log x * Real.log (2 * L + 1)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hec : 1 ≤ Real.exp c := Real.one_le_exp hc0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have h8L : 8 * (L : ℝ) ≤ (A₀ κ).card := by
    have e1 : x ^ (ε / 2) ≤ x := by
      calc x ^ (ε / 2) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hS.big.one_lt.le (by linarith [hS.big.ε_lt])
        _ = x := Real.rpow_one x
    nlinarith
  set N₀ := (A₀ κ).card / (4 * L) with hN₀
  have hN₀1 : ((A₀ κ).card : ℝ) / (8 * L) ≤ N₀ := by
    have e1 := Nat.lt_div_mul_add (a := (A₀ κ).card) (b := 4 * L) (by omega)
    have e2 : ((A₀ κ).card : ℝ) < N₀ * (4 * L) + 4 * L := by rw [hN₀]; exact_mod_cast e1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hN₀0 : 0 < N₀ := by
    have : (1 : ℝ) ≤ N₀ := le_trans ((le_div_iff₀ (by positivity)).2 (by linarith)) hN₀1
    exact_mod_cast (show (0 : ℝ) < N₀ by linarith)
  obtain ⟨T, hT, hrf, hTc⟩ := RelFree.exists_six L N₀ hL2 hN₀0
  refine ⟨g, T, hgmem, hord, fun s hs => ?_, hrf, ?_⟩
  · calc 4 * L * s < 4 * L * N₀ := Nat.mul_lt_mul_of_pos_left (hT s hs) (by omega)
      _ ≤ (A₀ κ).card := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  · -- the density
    have hN₀x : Real.log N₀ ≤ 3 * Real.log x := by
      have e1 : (N₀ : ℝ) ≤ x ^ 3 := by
        have : N₀ ≤ (A₀ κ).card := Nat.div_le_self _ _
        have e2 : ((A₀ κ).card : ℝ) ≤ Fintype.card S.A := by exact_mod_cast Finset.card_le_univ _
        have : (N₀ : ℝ) ≤ (A₀ κ).card := by exact_mod_cast this
        linarith [hS.card_le_cube]
      calc Real.log N₀ ≤ Real.log (x ^ 3) := Real.log_le_log (by exact_mod_cast hN₀0) e1
        _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
    have hlogL : 0 ≤ Real.log (2 * L + 1) := Real.log_nonneg (by linarith)
    have hexp : Real.exp (-c) ≤ Real.exp (-6 * √(Real.log N₀ * Real.log (2 * L + 1))) := by
      apply Real.exp_le_exp.2
      rw [hc, neg_mul, neg_le_neg_iff]
      gcongr
    have hT1 : (N₀ : ℝ) * Real.exp (-c) ≤ T.card := le_trans (by gcongr) hTc
    -- `|A₀|·x^{−ε/2} ≤ N₀e^{−c}`
    have hP0 : 0 < x ^ (ε / 2) := Real.rpow_pos_of_pos hx0 _
    have hQ0 : 0 < x ^ (ε / 100) := Real.rpow_pos_of_pos hx0 _
    have h2 : ((A₀ κ).card : ℝ) ≤ x ^ (ε / 2) * (N₀ * Real.exp (-c)) := by
      have e1 : 8 * (L : ℝ) ≤ x ^ (ε / 2) * Real.exp (-c) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
        exact hbeh
      have e2 : ((A₀ κ).card : ℝ) ≤ 8 * L * N₀ := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * L)).1 hN₀1
        linarith
      have e3 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
      nlinarith
    -- `x^{−ε}·x^{ε/2}·x^{ε/100} ≤ 1`
    have h3 : x ^ (-ε) * (x ^ (ε / 2) * x ^ (ε / 100)) ≤ 1 := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hS.big.one_lt.le (by linarith [hS.big.ε_pos])
    have h4 : 0 ≤ x ^ (-ε) := Real.rpow_nonneg hx0.le _
    have h5 : 0 ≤ (N₀ : ℝ) * Real.exp (-c) := by positivity
    calc x ^ (-ε) * Fintype.card S.A ≤ x ^ (-ε) * (x ^ (ε / 100) * (A₀ κ).card) := by gcongr
      _ ≤ x ^ (-ε) * (x ^ (ε / 100) * (x ^ (ε / 2) * (N₀ * Real.exp (-c)))) := by gcongr
      _ = (x ^ (-ε) * (x ^ (ε / 2) * x ^ (ε / 100))) * (N₀ * Real.exp (-c)) := by ring
      _ ≤ 1 * (N₀ * Real.exp (-c)) := by gcongr
      _ ≤ T.card := by rw [one_mul]; exact hT1

/-- **An admissible design at `x`**, for a setting meeting the setting-level clauses with `A₀` cyclic, Behrend's
comparison at `x` and split primes: the tops (`exists_tops`), the thick set (`exists_thick`), `a_t = ⌈a⌉`,
`b_t = ⌈b′⌉`, `s* ∈ T`, the shifts of `exists_shift_RU`, then `buildDesign`. -/
theorem exists_design [IsCyclic κ.ker]
    (hbeh : 8 * scLw x ε * Real.exp (6 * √(3 * Real.log x * Real.log (2 * scLw x ε + 1))) ≤ x ^ (ε / 2))
    (hg : ∃ g₀ g₁ : ℕ, g₀.Prime ∧ g₁.Prime ∧ g₀ ≠ g₁ ∧ (∀ g ∈ [g₀, g₁],
      ((designK x ε : ℝ) * Real.exp (x ^ ε)) ^ 8 ≤ g ∧ (g : ℝ) ≤ 2 * ((designK x ε : ℝ) * Real.exp (x ^ ε)) ^ 8 ∧
      ∃ α β : ℤ, 4 * (g : ℤ) = α ^ 2 + S.d * β ^ 2 ∧ (S.N : ℤ) ∣ β ∧ α ≡ β + 2 [ZMOD 2 * S.N]) ∧
      Disjoint (ExcSet (designK x ε + designM x ε - 1) g₀) (ExcSet (designK x ε + designM x ε - 1) g₁)) :
    ∃ Dg : SharpDesign S κ x ε (((S.N : ℝ) * x) ^ Real.log x), Dg.Adm := by
  have hx := hS.big.x_ge
  have hx0 := hS.big.pos
  obtain ⟨TT, hTT, hge, hle⟩ := hS.exists_tops
  obtain ⟨a₀, T, ha₀, hord, hrange, hrf, hcard⟩ := hS.exists_thick hbeh
  obtain ⟨sstar, hs⟩ : T.Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (0 : ℝ) < Fintype.card S.A := Nat.cast_pos.2 Fintype.card_pos
    have h2 : (0 : ℝ) < x ^ (-ε) * Fintype.card S.A := mul_pos (Real.rpow_pos_of_pos hx0 _) h1
    exact_mod_cast h2.trans_le hcard
  -- the scales `⌈a⌉` and the top shifts `⌈b′⌉`
  have ha : ∀ t ∈ TT, scA x ε ≤ ((fun _ => ⌈scA x ε⌉ : S.A → ℤ) t : ℝ) ∧
      ((fun _ => ⌈scA x ε⌉ : S.A → ℤ) t : ℝ) ≤ scA x ε + scA x ε / (designK x ε * x ^ 13) := by
    intro t _
    have hk := hS.big.designK_le
    have hb := hS.big.b_ge'
    have h1 : (designK x ε : ℝ) * x ^ 13 ≤ scA x ε := by
      have e1 : (designK x ε : ℝ) * x ^ 13 ≤ 2 * x ^ 18 := by nlinarith [pow_pos hx0 13]
      have e2 : x ^ 17 * 2 ≤ x ^ 17 * x ^ 833 :=
        mul_le_mul_of_nonneg_left (le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num)))
          (by positivity)
      unfold scA
      nlinarith [pow_pos hx0 17]
    have h2 : 1 ≤ scA x ε / (designK x ε * x ^ 13) := by
      rw [le_div_iff₀ (by nlinarith [pow_pos hx0 13])]
      linarith
    exact ⟨Int.le_ceil _, by linarith [Int.ceil_lt_add_one (scA x ε)]⟩
  have hb : ∀ t ∈ TT, scB' x ε ≤ ((fun _ => ⌈scB' x ε⌉ : S.A → ℤ) t : ℝ) ∧
      ((fun _ => ⌈scB' x ε⌉ : S.A → ℤ) t : ℝ) ≤ scB' x ε * (1 + x ^ (-(1 / 4 : ℝ))) := by
    intro t _
    have h1 : x ^ (-1 : ℝ) ≤ x ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hS.big.one_lt.le (by norm_num)
    rw [Real.rpow_neg_one] at h1
    have h2 := hS.big.b'_ge
    have h3 : 1 ≤ scB' x ε * x⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hx0]
      have : x ^ 1 ≤ x ^ 441 := pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h4 : scB' x ε * x⁻¹ ≤ scB' x ε * x ^ (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (scB'_pos ε hx0).le
    exact ⟨Int.le_ceil _, by linarith [Int.ceil_lt_add_one (scB' x ε)]⟩
  have hyp := hS.buildHyp (TT := TT.image (S.twA κ * ·)) (aZ := (fun _ => ⌈scA x ε⌉) ∘ (S.twA κ * ·))
    (bT := (fun _ => ⌈scB' x ε⌉) ∘ (S.twA κ * ·)) (fun _ hy => (ha _ (S.twA_mul_mem_of_mem_image κ hy)).1)
    (fun _ hy => (hb _ (S.twA_mul_mem_of_mem_image κ hy)).1)
  have hstar : ∀ u, placeKind (TT.image (S.twA κ * ·)) (T.image (a₀ ^ ·)) u (designStar a₀ sstar u) = .thick :=
    fun u => placeKind_eq_thick.2 (Finset.mem_image.2 ⟨a₀ ^ sstar, Finset.mem_image_of_mem _ hs, rfl⟩)
  obtain ⟨σ, hσ, hru⟩ := exists_shift_RU hyp hstar (dvd_mul_right _ _)
  obtain ⟨g₀, g₁, hg₀, hg₁, hne, hsplit, hexc⟩ := hg
  let pr : DesignPar S := ⟨fun _ => ⌈scA x ε⌉, fun _ => ⌈scB' x ε⌉, a₀, T, sstar, σ⟩
  have hI : BuildOk hS TT pr g₀ g₁ :=
    ⟨hTT, hge, hle, ha, hb, ha₀, hord, hrange, hrf, hcard, hs, hσ, fun _ => hru, hg₀, hg₁, hne, hsplit, hexc⟩
  exact ⟨buildDesign hS TT pr g₀ g₁ hI, buildDesign_adm hS TT pr g₀ g₁ hI⟩

end Setting.DesignAdm

/-! ## The parameters of the frontier -/

/-- `(−d/p) = 1` for `p` dividing `d + 1`, as `−d ≡ 1 (mod p)`. -/
theorem jacobiSym_neg_eq_one {d p : ℕ} (h : p ∣ d + 1) : jacobiSym (-(d : ℤ)) p = 1 := by
  have hm : -(d : ℤ) ≡ 1 [ZMOD p] := Int.modEq_iff_dvd.2 (by
    have := Int.natCast_dvd_natCast.2 h
    push_cast at this
    rwa [sub_neg_eq_add, add_comm])
  rw [jacobiSym.mod_left, hm.eq, ← jacobiSym.mod_left, jacobiSym.one_left]

/-- **The level**: for `y > 1`, some `e` has `y ≤ 2^e ≤ 2y` (the least `e` with `y ≤ 2^e`). -/
theorem exists_level {y : ℝ} (hy : 1 < y) : ∃ e : ℕ, y ≤ 2 ^ e ∧ (2 : ℝ) ^ e ≤ 2 * y := by
  classical
  have hex : ∃ e : ℕ, y ≤ 2 ^ e := (pow_unbounded_of_one_lt y one_lt_two).imp fun _ h => h.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hk : Nat.find hex with _ | e
  · have := Nat.find_spec hex
    rw [hk, pow_zero] at this
    linarith
  · have h1 := not_le.1 (Nat.find_min hex (show e < Nat.find hex by omega))
    rw [pow_succ]
    linarith

/-- **The setting of a pair meets the setting-level clauses** at `x ∈ [Y, Y²]`, for a pair of `WinPair ε Y`, a level
with `x^{2+8ε} ≤ 2^e ≤ 2x^{2+8ε}`, the growth package at `x` and `Y`, `ord χ, f ≤ x^{ε/100}`, `8f ≤ x`,
`log x ≥ 4`, and Littlewood's bound `|L′/L(1, χ)| ≤ M log log(N + 16)` with `M log x ≤ x^ε`. -/
theorem pairSetting_designAdm {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f) {Y : ℝ} {q d : ℕ}
    (hw : ZetaTwist.WinPair ε Y q d) (hpa : PairArith f q d) {e : ℕ} (hbig : DesignBig ε x)
    (hbigY : DesignBig ε Y) (hYx : Y ≤ x) (hxY : x ≤ Y ^ 2) (he1 : x ^ (2 + 8 * ε) ≤ 2 ^ e)
    (he2 : (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * ε)) (ho : (orderOf χ : ℝ) ≤ x ^ (ε / 100))
    (hf : (f : ℝ) ≤ x ^ (ε / 100)) (hf8 : 8 * (f : ℝ) ≤ x) (hl4 : 4 ≤ Real.log x) {M : ℝ} (hM0 : 0 ≤ M)
    (hMb : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsQuadratic → χ ≠ 1 →
      ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
        M * Real.log (Real.log (N + 16)))
    (hMx : M * Real.log x ≤ x ^ ε) : (pairSetting χ hpa e).DesignAdm (pairChar χ hpa e) x ε := by
  have hx0 := hbig.pos
  have hY0 := hbigY.pos
  have hlY := hbigY.one_le_log
  have hl := hbig.one_le_log
  have ho' : (orderOf (pairChar χ hpa e) : ℝ) ≤ x ^ (ε / 100) := by
    rw [(pairChar_lifts χ hpa e).orderOf_eq]
    exact ho
  have hn1 : (2 : ℝ) ^ e ≤ Fintype.card (pairSetting χ hpa e).A := by exact_mod_cast two_pow_le_card_A χ hpa e
  have hxY' : x ^ (ε / 10) ≤ Y ^ (ε / 5) := by
    calc x ^ (ε / 10) ≤ (Y ^ 2) ^ (ε / 10) := Real.rpow_le_rpow hx0.le hxY (by linarith [hbig.ε_pos])
      _ = Y ^ (ε / 5) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]; ring_nf
  have hYx5 : Y ^ (ε / 5) ≤ x ^ (ε / 5) := Real.rpow_le_rpow hY0.le hYx (by linarith [hbig.ε_pos])
  have hlYx : Real.log Y ≤ Real.log x := Real.log_le_log hY0 hYx
  have hd2 : Y ^ (ε / 5) ≤ Y ^ (ε / 5) * Real.log Y ^ 2 :=
    le_mul_of_one_le_right (Real.rpow_nonneg hY0.le _) (one_le_pow₀ hlY)
  have hdvd : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (ε / 10) → p ∣ d + 1 := by
    intro p hp hpx
    rcases eq_or_ne p 2 with rfl | hp2
    · have := hw.d_mod
      omega
    · exact hw.small_dvd p hp hp2 (hpx.trans hxY')
  refine ⟨hbig, he1.trans hn1, ?_, ho', ?_, hw.d_mod, hw.q_mod, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|A| = o|A₀| ≤ x^{ε/100}·2^e`
    have h1 : (Fintype.card (pairSetting χ hpa e).A : ℝ) =
        orderOf (pairChar χ hpa e) * (A₀ (pairChar χ hpa e)).card := by exact_mod_cast card_A_eq _
    have h2 : ((A₀ (pairChar χ hpa e)).card : ℝ) ≤ 2 ^ e := by exact_mod_cast card_A₀_le χ hpa e
    have h3 : x ^ (2 + 8 * ε + ε / 100) = x ^ (ε / 100) * x ^ (2 + 8 * ε) := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [h1, h3]
    calc (orderOf (pairChar χ hpa e) : ℝ) * (A₀ (pairChar χ hpa e)).card ≤ x ^ (ε / 100) * (2 * x ^ (2 + 8 * ε)) :=
          mul_le_mul ho' (h2.trans he2) (Nat.cast_nonneg _) (Real.rpow_nonneg hx0.le _)
      _ = 2 * (x ^ (ε / 100) * x ^ (2 + 8 * ε)) := by ring
  · -- `QS ≤ 4·2^e·f ≤ 4|A|x^{ε/100}`
    have h1 : ((pairSetting χ hpa e).QS : ℝ) ≤ 4 * 2 ^ e * f := by exact_mod_cast QS_le χ hpa e
    calc ((pairSetting χ hpa e).QS : ℝ) ≤ 4 * 2 ^ e * f := h1
      _ ≤ 4 * Fintype.card (pairSetting χ hpa e).A * x ^ (ε / 100) := by gcongr
  · -- `log q > Y^{ε/5}/2 ≥ x^{ε/10}/2`
    have := hw.q_size.1
    show x ^ (ε / 10) / 2 < Real.log q
    linarith
  · -- `log d > Y^{ε/5}log² Y/2 ≥ x^{ε/10}/2`
    have := hw.d_size.1
    show x ^ (ε / 10) / 2 < Real.log d
    linarith
  · exact jacobiSym_neg_eq_one hw.q_dvd
  · exact fun p hp hpx => jacobiSym_neg_eq_one (hdvd p hp hpx)
  · -- `log N ≤ log(4·2^e·f) + log q + log d ≤ 4 log x + x^{ε/5} + x^{ε/5}log² x`
    have h1 := log_N_le χ hpa e
    have h2 : Real.log (4 * 2 ^ e * f) ≤ 4 * Real.log x := by
      have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast NeZero.one_le
      have e3 : x ^ (2 + 8 * ε) ≤ x ^ 3 := hbig.rpow_le_npow 3 (by push_cast; linarith [hbig.ε_lt])
      have e4 : (4 : ℝ) * 2 ^ e * f ≤ x ^ 4 := by
        calc (4 : ℝ) * 2 ^ e * f ≤ 4 * (2 * x ^ 3) * f := by gcongr; linarith
          _ = x ^ 3 * (8 * f) := by ring
          _ ≤ x ^ 3 * x := by gcongr
          _ = x ^ 4 := by ring
      calc Real.log (4 * 2 ^ e * f) ≤ Real.log (x ^ 4) := Real.log_le_log (by positivity) e4
        _ = 4 * Real.log x := by rw [Real.log_pow]; norm_num
    have h3 := hw.q_size.2
    have h4 := hw.d_size.2
    have h5 : Real.log Y ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ (by linarith) hlYx 2
    have h6 : Y ^ (ε / 5) * Real.log Y ^ 2 ≤ x ^ (ε / 5) * Real.log x ^ 2 :=
      mul_le_mul hYx5 h5 (by positivity) (Real.rpow_nonneg hx0.le _)
    have h7 : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hbig.one_lt.le (by linarith [hbig.ε_pos])
    have h8 : 4 * Real.log x ≤ x ^ (ε / 5) * Real.log x ^ 2 := by nlinarith
    have h9 : x ^ (ε / 5) ≤ x ^ (ε / 5) * Real.log x ^ 2 :=
      le_mul_of_one_le_right (by linarith) (one_le_pow₀ hl)
    show Real.log (pairSetting χ hpa e).N ≤ _
    linarith
  · -- `|Re L′/L(1, χ_d)| ≤ M log log(d + 16) ≤ M log x ≤ x^ε`
    have hd : (pairSetting χ hpa e).d = d := rfl
    have hq : MulChar.IsQuadratic (legChar (pairSetting χ hpa e).d) :=
      (quadraticChar_isQuadratic _).comp (Int.castRingHom ℂ)
    have hne : legChar (pairSetting χ hpa e).d ≠ 1 :=
      (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).2
        (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact (pairSetting χ hpa e).d_ne_two))
    have h1 := hMb _ _ hq hne
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hw.d_prime.one_lt.le
    have hlog : Real.log ((pairSetting χ hpa e).d + 16) ≤ x := by
      rw [hd]
      have e1 : Real.log ((d : ℝ) + 16) ≤ Real.log 17 + Real.log d := by
        rw [← Real.log_mul (by norm_num) (by linarith)]
        exact Real.log_le_log (by linarith) (by linarith)
      have e2 : Real.log 17 ≤ 16 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 by norm_num)
        linarith
      have e3 := hw.d_size.2
      have h5 : Real.log Y ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ (by linarith) hlYx 2
      have e4 : Y ^ (ε / 5) * Real.log Y ^ 2 ≤ x ^ (ε / 5) * Real.log x ^ 2 :=
        mul_le_mul hYx5 h5 (by positivity) (Real.rpow_nonneg hx0.le _)
      have e5 : x ^ (ε / 5) * Real.log x ^ 2 ≤ 3 * x ^ (ε / 5) * Real.log x ^ 3 := by
        have : Real.log x ^ 2 ≤ Real.log x ^ 3 := pow_le_pow_right₀ hl (by norm_num)
        have : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
        nlinarith [sq_nonneg (Real.log x)]
      have e6 := hbig.thin
      have e7 : x ^ (ε / 3) ≤ x := by
        calc x ^ (ε / 3) ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hbig.one_lt.le (by linarith [hbig.ε_lt])
          _ = x := Real.rpow_one x
      nlinarith
    have hll : Real.log (Real.log ((pairSetting χ hpa e).d + 16)) ≤ Real.log x := by
      have : 0 < Real.log ((pairSetting χ hpa e).d + 16 : ℝ) := Real.log_pos (by rw [hd]; linarith)
      exact Real.log_le_log this hlog
    rw [logDeriv_apply]
    calc |(deriv (DirichletCharacter.LFunction (legChar (pairSetting χ hpa e).d)) 1 /
          DirichletCharacter.LFunction (legChar (pairSetting χ hpa e).d) 1).re|
        ≤ ‖deriv (DirichletCharacter.LFunction (legChar (pairSetting χ hpa e).d)) 1 /
          DirichletCharacter.LFunction (legChar (pairSetting χ hpa e).d) 1‖ := Complex.abs_re_le_norm _
      _ ≤ M * Real.log (Real.log ((pairSetting χ hpa e).d + 16)) := h1
      _ ≤ M * Real.log x := mul_le_mul_of_nonneg_left hll hM0
      _ ≤ x ^ ε := hMx

/-- **`SharpPieces.params`** (design spec §4.1), from `ShortNorm`: `ε = min(ε₀, 1/52)/2`, `A = 2`, and for `Y` large
and a pair of `WinPair ε Y`, `Y′ = Y`; at every `x ∈ [Y, Y²]`, the setting of the pair at the level
`x^{2+8ε} ≤ 2^e ≤ 2x^{2+8ε}` (`pairSetting`, with `κ = pairChar` lifting `χ`) and an admissible design
(`exists_design`). The thresholds: the growth package, `ord χ, f ≤ x^{ε/100}`, `8f ≤ x`, `log x ≥ 4`,
`M log x ≤ x^ε` for Littlewood's `M`, Behrend's comparison, `ShortNorm`'s `x₀` (`exists_split_primes`), all at
`x ≥ Y`, and `f ≤ Y^{ε/5}/2` for `PairArith`. -/
theorem sharpParams (hS : ShortNorm) : Params fun Dg => Dg.Adm := by
  intro f _ χ _ ε₀ hε₀
  set ε := min ε₀ (1 / 52) / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεε₀ : ε < ε₀ := by have := min_le_left ε₀ (1 / 52); linarith
  have hε52 : ε < 1 / 52 := by have := min_le_right ε₀ (1 / 52); linarith
  refine ⟨ε, hε, hεε₀, 2, by norm_num, ?_⟩
  obtain ⟨M, hM0, hMb⟩ := Littlewood.norm_logDeriv_one_le
  obtain ⟨xs, hxs⟩ := exists_split_primes hS ε hε hε52
  have hMlog : ∀ᶠ x in atTop, M * Real.log x ≤ x ^ ε := by
    filter_upwards [(isLittleO_log_rpow_atTop hε).bound (show (0 : ℝ) < 1 / (M + 1) by positivity),
      eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    have h1 : M * Real.log x ≤ M * (1 / (M + 1) * x ^ ε) := mul_le_mul_of_nonneg_left hx hM0
    have h2 : M * (1 / (M + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) ε]
  have ev : ∀ᶠ x in atTop, DesignBig ε x ∧ (orderOf χ : ℝ) ≤ x ^ (ε / 100) ∧ (f : ℝ) ≤ x ^ (ε / 100) ∧
      8 * (f : ℝ) ≤ x ∧ 4 ≤ Real.log x ∧ M * Real.log x ≤ x ^ ε ∧ xs ≤ x ∧
      8 * scLw x ε * Real.exp (6 * √(3 * Real.log x * Real.log (2 * scLw x ε + 1))) ≤ x ^ (ε / 2) := by
    filter_upwards [eventually_designBig ε hε hε52,
      (tendsto_rpow_atTop (show 0 < ε / 100 by positivity)).eventually_ge_atTop (orderOf χ : ℝ),
      (tendsto_rpow_atTop (show 0 < ε / 100 by positivity)).eventually_ge_atTop (f : ℝ),
      eventually_ge_atTop (8 * (f : ℝ)), Real.tendsto_log_atTop.eventually_ge_atTop 4, hMlog,
      eventually_ge_atTop xs, eventually_behrend (C := 6) (by norm_num) hε (by linarith)]
      with x h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 ev
  filter_upwards [eventually_ge_atTop x₁,
    (tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop (2 * (f : ℝ))] with Y hY hYf
  intro q d hw
  refine ⟨Y, ⟨le_rfl, by norm_num⟩, fun x hx => ?_⟩
  have hbY := (hx₁ Y hY).1
  obtain ⟨hbig, ho, hf, hf8, hl4, hMx, hxs', hbeh⟩ := hx₁ x (hY.trans hx.1)
  have hpa : PairArith f q d := hw.pairArith (by linarith)
  obtain ⟨e, he1, he2⟩ := exists_level (Real.one_lt_rpow hbig.one_lt (by linarith : (0 : ℝ) < 2 + 8 * ε))
  have hS' := pairSetting_designAdm χ hw hpa hbig hbY hx.1 hx.2 he1 he2 ho hf hf8 hl4 hM0 hMb hMx
  refine ⟨pairSetting χ hpa e, pairChar χ hpa e, rfl, rfl, by have := hw.d_mod; show d % 4 = 3; omega,
    pairChar_lifts χ hpa e, ?_⟩
  refine hS'.exists_design hbeh (hxs x hxs' _ _ (designK x ε + designM x ε - 1) (designK x ε)
    (Fact.out : (pairSetting χ hpa e).d.Prime) (by have := hS'.d_mod; omega) hS'.hundred_le_d
    (pairSetting χ hpa e).d_dvd_N (NeZero.pos _) hS'.log_N_le ?_ ?_)
  · have := hbig.designK_le.1
    exact_mod_cast this
  · exact designRanks_r_le (pairSetting χ hpa e) hbig hS'.card_ge hS'.card_le

end ZetaBalance

#print axioms ZetaBalance.sharpParams
#print axioms ZetaBalance.buildDesign_adm
#print axioms ZetaBalance.Setting.DesignAdm.exists_design
