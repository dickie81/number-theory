import GainExponents

/-!
# The per-orbit inequality

A step of the proof of the sharp frontier (`SharpInputs`, the piece `gain`; module M-G7a of the gain's numbers): the
per-orbit inequality, which bounds the asks of the tops on one orbit at a prime `p` by the orbit's gain, in its served
and trivial-gain forms, and its sum over the orbits and the lifts (`gains_ge_ask`), which the losses read. The
definitions of the gain are `GainExponents`'; those of the orbits, `DesignOrbits`'.

**Definitions.** The ask of a top `s` at `p` in the gain's (twisted) coordinates,
`ask(s) = Σ_{e ∈ gainExps} (a_s/p^e − w_j(pos_p(1, s; e)))⁺` (`askE`); the tops whose ask the gain covers
(`coveredTops`: at the inert and signal `p ≤ X″` with `ord h_p` even, every top if `p` is a signal prime or `p ≥ X′`,
and the tops of the served orbits otherwise); the allowances of a served orbit, per top (`topAllow`, beyond
`2c₀·|gainExps|`) and per unit of `n_p` (`orbAllow`); the slacks per top (`slack1`) and per lift (`slack2`); and the
surplus `g(s, e) = min(ā_s/p^e, w_j(pos_p(1, s; e)) − 2c₀/p^e)` of a top at `e` (`surplus`).

**The per-orbit inequality** (`orbit_ineq`): at an inert `p` with `ord h_p` even, on **every** orbit of tops
(`topsOn p t₀`), `Σ_{tops} ask ≤ g^{sv} − pen − (⌈dep⌉ + D_p + 1) + sl + #tops·(2c₀·|gainExps| + topAllow) +
n_p·orbAllow`. With `κ_j = (k + (2j − 1)(t + 1))/2 ≥ 0`, so that `cap = w − κ_j + c₀`:
* L1 (`ask_term_le`): a term of a non-V top is at most `(ā_s/p^e − cap_{s,e})⁺ + 2c₀`, as the arguments differ by
  `2c₀/p^e + c₀ − κ_j ≤ 2c₀`;
* L2 (`ask_term_eq`): a term of a V-top is `ā_s/p^e − g(s, e)`, by `(A − B)⁺ = A − min(A, B)`, so
  `ask(s) ≤ γ_p·ā_s − Σ_e g(s, e)` (`askE_le_V`); with L1 this is the core
  `Σ_{tops} ask ≤ g^{sv} + sl − Σ_{V-tops} Σ_e g(s, e) + #(non-V tops)·2c₀·|gainExps|` (`sum_askE_le`);
* L3 (`vPrev_spec`, `odd_vDist`): the nearest V-top `y′ = vPrev p y`, at the distance `d = vDist p y ≠ 0`, is a V-top
  of the orbit of `y` with `y′·σ_p^d = y`; from a non-V top, `d` is odd when `ord σ_p` is even;
* L4 (`lt_pow_of_notMem_gainExps`): an odd `e ∉ gainExps` has `p^e > 2a`;
* L5 (`dep0_le`, the V-top surplus): `Σ_{non-V y} [d ≠ 0]·min(b_y, a_{y′}/p^d) ≤ Σ_{V-tops} Σ_e g(s, e) +
  #(non-V tops)·(c₀ + 1)`. A term with `d ∉ gainExps` is `≤ 1` (L3, L4); with `d ∈ gainExps` the partner of `y′` at
  `d` is the top `(1, y)`, of weight `≥ b_y + b′/x`, so the term is `≤ g(y′, d) + c₀`; and `y ↦ (y′, d)` is injective
  into the V-tops times `gainExps`;
* the penalty's terms at the non-V tops are `w̃_j(1, s) − b_s ≤ b′/x + η` (the top window), and the rest of `pen`,
  `dep` and `D_p` is the allowance (`⌈y⌉₊ ≤ Q + 1` for `y ≤ Q`, `Q ≥ 0`: `natCeil_le_add_one`; `n_p ≥ 1`).

**The trivial-gain form** (`orbit_ineq_tr`): at a signal `p`, or an inert `p ≥ X′`,
`Σ_{tops} ask ≤ g^{tr} + sl + #tops·2c₀·|gainExps|`. A collision costs no ask: there is none at a signal `p`, and at
an inert `p ≥ X′` its partner is a top, of weight `≥ b′(1 + 1/x) ≥ a_s/X′ ≥ a_s/p^e` (`ask_term_eq_zero_of_collides`);
the other terms obey L1.

**Summed** (`gains_ge_ask`): `Σ_j Σ_{covered tops} ask − m·#covered·slack₁ − m·slack₂ ≤ Σ_j G_j(p) − τ_p` at every
`p`. Off the inert and signal `p ≤ X″` of even order nothing is covered and `G = τ = 0`; at a signal `p` or `p ≥ X′`
no orbit is served (the candidates are inert and `< X′`) and `orbit_ineq_tr` holds on each; at an inert `p < X′` the
served orbits obey `orbit_ineq`, their depths make up `τ_p − e_p`, and the unserved orbits are dropped
(`g^{tr⁺} ≥ 0`). The orbits of the tops cover at most `2|A|` positions, `#basePts·n_p ≤ 2|A|`
(`card_basePts_mul_le`), which sums the slacks (`sum_sl_le`) and the per-orbit allowances.

**The design's facts used** (`SharpDesign.Adm.*`, from `Adm` and `FamAt`): `c₀ ≤ x^{437} ≤ w″ ≤ w` (`c0_le`,
`c0_le_wt`), `2c₀ ≤ a_t ≤ a(1 + 1/x) ≤ 2a` at the tops (`two_c0_le_a`, `a_le`, `a_le_two`), the top window
`b_y + b′/x ≤ w_j(1, y) ≤ b_y + b′/x + η` (`top_window`, from `hcFam_windows` at the design's top `(1, c·y)`: the
gain's `w_j(z)` reads `hc u` at `(z.1, c·z.2)`, `GainExponents.wt`), and `m ≥ 1` (`one_le_m`).

**Orbits** (in any finite abelian group): base points are fixed (`basePoint_basePoint`), `basePoint(t)·σ^i` sits at
the position `i` for `i < ord σ` (`orbitPos_basePoint_mul`), going back `d ≤ ord σ` positions and forward `d` returns
(`basePoint_mul_back`), a nonzero `prevV` is a distance to a V-position (`prevV_spec_of_ne_zero`), and it is odd from
an odd position when `n′` is even (`odd_of_back`).

**Against the spec.**
* No goodness and no Stage-2 clause is used: the per-orbit inequality holds on every orbit, with the per-orbit
  allowance `n_p·orbAllow`; only the definition of `prevV` and the evenness of `ord h_p` enter L5.
* The summand `1` of `topAllow` below `p₀` is not needed by `orbit_ineq` (the `3` of `orbAllow` and `n_p ≥ 1`
  suffice); it is kept, as the statements are the spec's.
-/

open Finset

namespace ZetaBalance

noncomputable section

/-! ## Orbits -/

section Orbits

variable {A : Type*} [CommGroup A] [Finite A]

/-- **Base points are fixed**: `basePoint σ (basePoint σ t) = basePoint σ t`. -/
theorem basePoint_basePoint (σ t : A) : basePoint σ (basePoint σ t) = basePoint σ t := by
  conv_rhs => rw [← basePoint_mul_orbitPos σ t, basePoint_mul_pow]

/-- **The base point of a point of the orbit**: `basePoint σ (basePoint σ t · σ^i) = basePoint σ t`. -/
theorem basePoint_basePoint_mul (σ t : A) (i : ℕ) : basePoint σ (basePoint σ t * σ ^ i) = basePoint σ t := by
  rw [basePoint_mul_pow, basePoint_basePoint]

/-- **The position is unique**: `orbitPos σ (basePoint σ t · σ^i) = i` for `i < ord σ`. -/
theorem orbitPos_basePoint_mul (σ t : A) {i : ℕ} (hi : i < orderOf σ) :
    orbitPos σ (basePoint σ t * σ ^ i) = i := by
  have h := basePoint_mul_orbitPos σ (basePoint σ t * σ ^ i)
  rw [basePoint_basePoint_mul, mul_right_inj] at h
  exact pow_injOn_Iio_orderOf (orbitPos_lt _ _) hi h

/-- **Going back `d` steps and forward `d` steps**: for `d ≤ ord σ`, the point at position
`(i + ord σ − d) mod ord σ`, `i = orbitPos σ t`, times `σ^d`, is `t`. -/
theorem basePoint_mul_back (σ t : A) {d : ℕ} (hd : d ≤ orderOf σ) :
    basePoint σ t * σ ^ ((orbitPos σ t + orderOf σ - d) % orderOf σ) * σ ^ d = t := by
  have hn := orderOf_pos σ
  have hi := orbitPos_lt σ t
  rw [mul_assoc, ← pow_add, ← pow_mod_orderOf σ, Nat.mod_add_mod,
    show orbitPos σ t + orderOf σ - d + d = orbitPos σ t + orderOf σ by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hi, basePoint_mul_orbitPos]

/-- **`prevV ≠ 0` is a distance to a V-position**: `1 ≤ d ≤ n′`, and the position `d` back is an even point. -/
theorem prevV_spec_of_ne_zero {n' : ℕ} {P : Finset ℕ} {i : ℕ} (h : prevV n' P i ≠ 0) :
    1 ≤ prevV n' P i ∧ prevV n' P i ≤ n' ∧ (i + n' - prevV n' P i) % n' ∈ P ∧
      Even ((i + n' - prevV n' P i) % n') := by
  unfold prevV at h ⊢
  split_ifs at h ⊢ with hne
  · have hm := min'_mem _ hne
    rw [mem_filter, mem_Icc] at hm
    exact ⟨hm.1.1, hm.1.2, hm.2.1, hm.2.2⟩
  · exact absurd rfl h

/-- **The parity of the distance**: from an odd position `i`, an even position `d` back (cyclically, `n′` even)
is at an odd distance `d ≤ n′`. -/
theorem odd_of_back {n' i d : ℕ} (hn : Even n') (hd : d ≤ n') (hi : ¬ Even i)
    (he : Even ((i + n' - d) % n')) : Odd d := by
  rw [Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hn)] at he
  rw [Nat.even_iff] at hn hi
  rw [Nat.odd_iff]
  omega

end Orbits

/-! ## Elementary facts -/

/-- **The exponents are odd**: `e ∈ gainExps` is `2i + 1`. -/
theorem odd_of_mem_gainExps {x ε : ℝ} {p e : ℕ} (he : e ∈ gainExps x ε p) : Odd e := by
  obtain ⟨i, -, rfl⟩ := mem_map.1 he
  exact ⟨i, rfl⟩

/-- **The exponents are positive.** -/
theorem one_le_of_mem_gainExps {x ε : ℝ} {p e : ℕ} (he : e ∈ gainExps x ε p) : 1 ≤ e := by
  obtain ⟨i, rfl⟩ := odd_of_mem_gainExps he
  omega

/-- **Beyond the exponents** (L4): an odd `e ∉ gainExps` has `p^e > 2a`, as `e ≥ 2(log_p⌈2a⌉ + 1) + 1` and
`⌈2a⌉ < p^{log_p⌈2a⌉ + 1}`. -/
theorem lt_pow_of_notMem_gainExps {x ε : ℝ} {p e : ℕ} (hp : 2 ≤ p) (ho : Odd e) (he : e ∉ gainExps x ε p) :
    2 * scA x ε < (p : ℝ) ^ e := by
  obtain ⟨i, rfl⟩ := ho
  have hi : Nat.log p ⌈2 * scA x ε⌉₊ + 1 ≤ i := by
    by_contra h
    exact he (mem_map.2 ⟨i, mem_range.2 (by omega), rfl⟩)
  have h1 := Nat.lt_pow_succ_log_self (by omega : 1 < p) ⌈2 * scA x ε⌉₊
  have h2 : p ^ (Nat.log p ⌈2 * scA x ε⌉₊).succ ≤ p ^ (2 * i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc 2 * scA x ε ≤ ⌈2 * scA x ε⌉₊ := Nat.le_ceil _
    _ < ((p ^ (2 * i + 1) : ℕ) : ℝ) := by exact_mod_cast h1.trans_le h2
    _ = (p : ℝ) ^ (2 * i + 1) := by push_cast; rfl

/-- `⌈y⌉₊ ≤ Q + 1` for `y ≤ Q`, `Q ≥ 0`. -/
theorem natCeil_le_add_one {y Q : ℝ} (h : y ≤ Q) (hQ : 0 ≤ Q) : (⌈y⌉₊ : ℝ) ≤ Q + 1 := by
  have h1 : ⌈y⌉₊ ≤ ⌈Q⌉₊ := Nat.ceil_le_ceil h
  have h2 := Nat.ceil_lt_add_one hQ
  have h3 : (⌈y⌉₊ : ℝ) ≤ ⌈Q⌉₊ := by exact_mod_cast h1
  linarith

/-- **The partner at an inert prime**: `pos_p(1, s; e) = (1, s·σ_p^e)`. -/
theorem Setting.pos_one_of_inert {S : Setting} (c : S.A) {p : ℕ} (hin : S.cls p = .inert) (s : S.A) (e : ℕ) :
    S.pos c p (1, s) e = (1, s * S.orbitStep c p ^ e) := by
  simp [Setting.pos, Setting.orbitStep, hin]

namespace SharpDesign

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} (Dg : SharpDesign S κ x ε X)

/-! ## Definitions -/

/-- **The ask of a top at `p`**, in the gain's (twisted) coordinates:
`Σ_{e ∈ gainExps} (a_s/p^e − w_j(pos_p(1, s; e)))⁺`. -/
def askE (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (s : S.A) : ℝ :=
  ∑ e ∈ gainExps x ε p, max (Dg.a s / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, s) e)) 0

open scoped Classical in
/-- **The tops whose ask the gain covers at `p`**: at an inert or signal `p ≤ X″` with `ord h_p` even, every top if
`p` is a signal prime or `p ≥ X′`, and otherwise the tops of the served orbits; none elsewhere. -/
def coveredTops (p : ℕ) : Finset S.A :=
  if p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∧ Even (orderOf (S.hPtw (S.twA κ) p)) then
    (if S.cls p = .signal ∨ scX' x ε ≤ p then Dg.TT
     else Dg.TT.filter fun t => basePoint (S.orbitStep (S.twA κ) p) t ∈ Dg.served p)
  else ∅

/-- **The per-top allowance** of a served orbit (beyond `2c₀·|gainExps|`). -/
def topAllow (p : ℕ) : ℝ :=
  if scP0 x Dg.R.k ≤ p then
    Dg.c0 + 1 + scB' x ε / x + Dg.eta +
      Kg.cκ₁ * (tilePar x ε Dg.R.k).N₁ * (scA x ε / (p : ℝ) ^ 2 + scLa x ε Dg.R.k * scA x ε / (p * Dg.R.k)) +
      Kg.cκ₂ * ((p : ℝ) ^ (tilePar x ε Dg.R.k).G' * Dg.cDep p + Dg.R.k * (p : ℝ) ^ (tilePar x ε Dg.R.k).G' +
        Dg.R.k * Real.logb p (scA x ε) + Dg.c0)
  else 1 + (tilePar x ε Dg.R.k).r * (2 * scB' x ε + Dg.c0) +
    Kg.ct * (tilePar x ε Dg.R.k).r * (scLa x ε Dg.R.k * scA x ε / (p * Dg.R.k) +
      scA x ε / (p : ℝ) ^ scL1 x Dg.R.k p + 2 * scB' x ε + 2 * Dg.c0 +
      Dg.R.k * (p : ℝ) ^ (tilePar x ε Dg.R.k).G')

/-- **`slack₁(p)`**: `2c₀·|gainExps|`, plus `topAllow` at the candidates. -/
def slack1 (p : ℕ) : ℝ :=
  2 * Dg.c0 * (gainExps x ε p).card + if p ∈ S.cand κ x ε Dg.R.k then Dg.topAllow p else 0

/-- **The per-orbit allowance** of a served orbit, per unit of `n_p`. -/
def orbAllow (p : ℕ) : ℝ :=
  if scP0 x Dg.R.k ≤ p then
    Kg.cPr * (scW'' S x ε + Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) + 2 * Dg.c0 +
      Kg.cD₁ * 40 * scδ₁ x ε * x ^ 26 * (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) *
        Real.logb p (scA x ε) + 3
  else (tilePar x ε Dg.R.k).r * (scW'' S x ε + Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) +
    4 * (tilePar x ε Dg.R.k).r * Dg.c0 +
    Kg.cD₂ * 40 * scδ₁ x ε * (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 3 + ((tilePar x ε Dg.R.k).r : ℝ) ^ 5 +
      (Dg.R.k : ℝ) ^ 2) * Real.logb p (scA x ε) +
    (tilePar x ε Dg.R.k).r * 40 * scδ₁ x ε * (2 * scB' x ε + 2 * Dg.c0) + 3

/-- **`slack₂(p)`** (per lift): the orbits' slacks `Σ_{t₀} sl`, and at the candidates the orbit allowances and
`e_p`. -/
def slack2 (p : ℕ) : ℝ :=
  Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
    Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2 +
    if p ∈ S.cand κ x ε Dg.R.k then 2 * Fintype.card S.A * Dg.orbAllow p + Dg.eSand p else 0

/-- **The surplus of a top at the exponent `e`**: `g(s, e) = min(ā_s/p^e, w_j(pos_p(1, s; e)) − 2c₀/p^e)`, what a
V-top's served gain `γ_p·ā_s` keeps beyond its ask at `e`. -/
def surplus (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (s : S.A) (e : ℕ) : ℝ :=
  min (Dg.abar s / (p : ℝ) ^ e) (Dg.wt u J (S.pos (S.twA κ) p (1, s) e) - 2 * Dg.c0 / (p : ℝ) ^ e)

variable {Dg}

/-! ## The design's facts -/

namespace Adm

variable (hA : Dg.Adm)
include hA

/-- `x ≥ 1` at an admissible design. -/
theorem one_le_x : 1 ≤ x := hA.big.one_lt.le

/-- **`c₀ ≤ x^{437}`**: `c₀ = 16kΔ ≤ 16·2x⁵·2x`. -/
theorem c0_le : Dg.c0 ≤ x ^ 437 := by
  have hx := hA.big.x_ge
  obtain ⟨-, hk⟩ := hA.big.designK_le
  rw [← hA.k_eq] at hk
  have hΔ := hA.big.designΔ_mem.2
  have h6 : 64 * x ^ 6 ≤ x ^ 437 := by
    have : x ^ 437 = x ^ 6 * x ^ 431 := by ring
    rw [this]
    have : 64 ≤ x ^ 431 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
    nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 6]
  unfold c0
  calc 16 * (Dg.R.k : ℝ) * designΔ x ≤ 16 * (2 * x ^ 5) * (2 * x) := by
        gcongr
    _ = 64 * x ^ 6 := by ring
    _ ≤ x ^ 437 := h6

/-- **Every weight is at least `c₀`**: `w ≥ w″ ≥ x^{437} ≥ c₀`. -/
theorem c0_le_wt (u : S.A) (J : Fin Dg.R.m) (z : Φ S.A) : Dg.c0 ≤ Dg.wt u J z :=
  hA.c0_le.trans (hA.toDesignAdm.w''_ge.trans (hA.e_mem u (z.1, S.twA κ * z.2) J).1)

/-- **`2c₀ ≤ a_t`** at a top: `a_t ≥ a = x·b ≥ x^{850}`. -/
theorem two_c0_le_a {pr : DesignPar S} (hF : Dg.FamAt pr) {t : S.A} (ht : t ∈ Dg.TT) :
    2 * Dg.c0 ≤ Dg.a t := by
  have hx := hA.big.x_ge
  have h1 := hA.c0_le
  have h2 := hA.big.b_ge'
  have h3 : 2 * x ^ 437 ≤ x ^ 850 := by
    have : x ^ 850 = x ^ 437 * x ^ 413 := by ring
    rw [this]
    have : 2 ≤ x ^ 413 := le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
    nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 437]
  have h4 : scB x ε ≤ scA x ε := by
    unfold scA
    nlinarith [Real.exp_pos (scL x ε), show scB x ε = Real.exp (scL x ε) from rfl]
  rw [hF.a_eq]
  linarith [(hF.a_mem t ht).1]

/-- **`a_t ≤ a(1 + 1/x)`** at a top: `a_t ≤ a + a/(kx^{13})` and `kx^{13} ≥ x`. -/
theorem a_le {pr : DesignPar S} (hF : Dg.FamAt pr) {t : S.A} (ht : t ∈ Dg.TT) :
    Dg.a t ≤ scA x ε + scA x ε / x := by
  have hx := hA.big.x_ge
  have hk : (1 : ℝ) ≤ Dg.R.k := Dg.one_le_k
  have ha : 0 ≤ scA x ε := (scA_pos ε hA.big.pos).le
  have h1 : x ≤ Dg.R.k * x ^ 13 := by
    have : x ≤ x ^ 13 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith [pow_pos (show (0 : ℝ) < x by linarith) 13]
  have h2 : scA x ε / (Dg.R.k * x ^ 13) ≤ scA x ε / x := div_le_div_of_nonneg_left ha (by linarith) h1
  rw [hF.a_eq]
  linarith [(hF.a_mem t ht).2]

/-- **`a_t ≤ 2a`** at a top. -/
theorem a_le_two {pr : DesignPar S} (hF : Dg.FamAt pr) {t : S.A} (ht : t ∈ Dg.TT) :
    Dg.a t ≤ 2 * scA x ε := by
  have hx := hA.big.x_ge
  have ha : 0 ≤ scA x ε := (scA_pos ε hA.big.pos).le
  have : scA x ε / x ≤ scA x ε := div_le_self ha (by linarith)
  linarith [hA.a_le hF ht]

/-- **The top window**: `b_y + b′/x ≤ w_j(1, y) ≤ b_y + b′/x + η` at a top `y` (`hcFam_windows`): `w_j(1, y)` is the
weight of `hc u` at the design's top `(1, c·y)`, which carries `b_{c·(c·y)} = b_y` (twisted tops). -/
theorem top_window {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {y : S.A}
    (hy : y ∈ Dg.TT) :
    (pr.bT y : ℝ) + scB' x ε / x ≤ Dg.wt u J (1, y) ∧ Dg.wt u J (1, y) ≤ pr.bT y + scB' x ε / x + Dg.eta := by
  have hHσ : ∀ u, pr.σ u ≤ designH S x := fun u => by
    have h1 : (pr.σ u : ℝ) < designH S x :=
      lt_of_lt_of_le (by exact_mod_cast hF.σ_lt u) hA.toDesignAdm.designH_mem.1
    exact_mod_cast h1.le
  obtain ⟨Wt, -⟩ := hcFam_windows hF.hyp (T2 := Dg.T2) (ρstar := designStar pr.a₀ pr.sstar)
    (bR := scB x ε) (wR := scW'' S x ε) (pR := scB' x ε / x) rfl rfl rfl hHσ u (1, S.twA κ * y) J
  have h := Wt (placeKind_eq_top.2 ⟨rfl, Finset.mem_image_of_mem _ hy⟩)
  simp only [Function.comp_apply, S.twA_mul_twA_mul κ] at h
  unfold wt eta
  rw [Setting.Ranks.wj, hF.hc_eq u]
  constructor
  · exact h.1
  · calc _ ≤ _ := h.2
      _ = _ := by ring

/-- **`m ≥ 1`** at an admissible design. -/
theorem one_le_m : (1 : ℝ) ≤ Dg.R.m := by
  have h := hA.m_mem.1
  have h0 : 0 < x ^ (1 / 2 - ε / 16) := Real.rpow_pos_of_pos hA.big.pos _
  have : Dg.R.m ≠ 0 := by
    intro h'
    rw [h', Nat.cast_zero] at h
    linarith
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

end Adm

/-! ## The ask, term by term -/

/-- `2c₀/p^e ≤ c₀` for `p ≥ 2`, `e ≥ 1`. -/
theorem two_c0_div_le {p e : ℕ} (hp : 2 ≤ p) (he : 1 ≤ e) : 2 * Dg.c0 / (p : ℝ) ^ e ≤ Dg.c0 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpe : (2 : ℝ) ≤ (p : ℝ) ^ e := h2.trans (le_self_pow₀ (by linarith) (by omega))
  calc 2 * Dg.c0 / (p : ℝ) ^ e ≤ 2 * Dg.c0 / 2 :=
        div_le_div_of_nonneg_left (by linarith [Dg.c0_nonneg]) (by norm_num) hpe
    _ = Dg.c0 := by ring

/-- **The shifted weight is at most the weight**: the shift `(k + (2j − 1)(t + 1))/2` is nonnegative. -/
theorem wsh_le_wt (u : S.A) (J : Fin Dg.R.m) (z : Φ S.A) : Dg.wsh u J z ≤ Dg.wt u J z := by
  unfold wsh
  have : (0 : ℝ) ≤ ((Dg.R.k : ℝ) + (2 * (J : ℝ) + 1) * ((Dg.R.t : ℝ) + 1)) / 2 := by positivity
  linarith

/-- **L1, a term of a non-V top**: `(a_s/p^e − w)⁺ ≤ (ā_s/p^e − cap_{s,e})⁺ + 2c₀`, as the difference of the
arguments is `2c₀/p^e + c₀ − (k + (2j − 1)(t + 1))/2 ≤ 2c₀`. -/
theorem ask_term_le (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) (s : S.A) {e : ℕ} (he : 1 ≤ e) :
    max (Dg.a s / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, s) e)) 0 ≤
      max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 + 2 * Dg.c0 := by
  have h1 := Dg.two_c0_div_le hp he
  have h2 := Dg.wsh_le_wt u J (S.pos (S.twA κ) p (1, s) e)
  have h3 : Dg.abar s / (p : ℝ) ^ e = Dg.a s / (p : ℝ) ^ e - 2 * Dg.c0 / (p : ℝ) ^ e := by
    unfold abar; rw [sub_div]
  have h4 : Dg.cap u J p s e = Dg.wsh u J (S.pos (S.twA κ) p (1, s) e) + Dg.c0 := rfl
  have h0 := Dg.c0_nonneg
  refine max_le ?_ (by linarith [le_max_right (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0])
  linarith [le_max_left (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0]

/-- **L2, a term of a V-top**: `(a_s/p^e − w)⁺ = ā_s/p^e − g(s, e)`, by `(A − B)⁺ = A − min(A, B)`. -/
theorem ask_term_eq (u : S.A) (J : Fin Dg.R.m) (p : ℕ) (s : S.A) (e : ℕ) :
    max (Dg.a s / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, s) e)) 0 =
      Dg.abar s / (p : ℝ) ^ e - Dg.surplus u J p s e := by
  have h3 : Dg.abar s / (p : ℝ) ^ e = Dg.a s / (p : ℝ) ^ e - 2 * Dg.c0 / (p : ℝ) ^ e := by
    unfold abar; rw [sub_div]
  unfold surplus
  rcases le_total (Dg.abar s / (p : ℝ) ^ e) (Dg.wt u J (S.pos (S.twA κ) p (1, s) e) - 2 * Dg.c0 / (p : ℝ) ^ e)
    with h | h
  · rw [min_eq_left h, sub_self, max_eq_right (by linarith)]
  · rw [min_eq_right h, max_eq_left (by linarith)]
    linarith

/-- **The surplus is nonnegative** at a top: `ā_s ≥ 0` and `w ≥ c₀ ≥ 2c₀/p^e`. -/
theorem surplus_nonneg (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : 2 ≤ p) {s : S.A} (hs : s ∈ Dg.TT) {e : ℕ} (he : 1 ≤ e) : 0 ≤ Dg.surplus u J p s e := by
  have h1 := Dg.two_c0_div_le hp he
  have h2 := hA.c0_le_wt u J (S.pos (S.twA κ) p (1, s) e)
  have h3 : 0 ≤ Dg.abar s := by unfold abar; linarith [hA.two_c0_le_a hF hs]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  exact le_min (div_nonneg h3 (pow_nonneg hp0.le _)) (by linarith)

/-- **The ask of a non-V top** (L1): `ask(s) ≤ Σ_e (ā_s/p^e − cap_{s,e})⁺ + 2c₀·|gainExps|`. -/
theorem askE_le_nonV (u : S.A) (J : Fin Dg.R.m) {p : ℕ} (hp : 2 ≤ p) (s : S.A) :
    Dg.askE u J p s ≤ ∑ e ∈ gainExps x ε p, max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 +
      2 * Dg.c0 * (gainExps x ε p).card := by
  unfold askE
  calc _ ≤ ∑ e ∈ gainExps x ε p, (max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 + 2 * Dg.c0) :=
        sum_le_sum fun e he => Dg.ask_term_le u J hp s (one_le_of_mem_gainExps he)
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]; ring

/-- **The ask of a V-top** (L2): `ask(s) ≤ γ_p·ā_s − Σ_e g(s, e)`. -/
theorem askE_le_V (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : 2 ≤ p) {s : S.A} (hs : s ∈ Dg.TT) :
    Dg.askE u J p s ≤ gamP p * Dg.abar s - ∑ e ∈ gainExps x ε p, Dg.surplus u J p s e := by
  have h3 : 0 ≤ Dg.abar s := by unfold abar; linarith [hA.two_c0_le_a hF hs]
  unfold askE
  simp only [Dg.ask_term_eq u J p s, sum_sub_distrib]
  linarith [sum_gainExps_le (x := x) (ε := ε) hp h3]

/-! ## The nearest V-top and its surplus -/

/-- **L3, the nearest V-top**: if `d = vDist p y ≠ 0`, then `y′ = vPrev p y` is a top on the orbit of `y`, V-type,
with `y′·σ_p^d = y`, and `1 ≤ d ≤ ord σ_p`. -/
theorem vPrev_spec (p : ℕ) {y : S.A} (hd : Dg.vDist p y ≠ 0) :
    Dg.vPrev p y ∈ Dg.TT ∧
      basePoint (S.orbitStep (S.twA κ) p) (Dg.vPrev p y) = basePoint (S.orbitStep (S.twA κ) p) y ∧
      IsVType (S.orbitStep (S.twA κ) p) (Dg.vPrev p y) ∧
      Dg.vPrev p y * S.orbitStep (S.twA κ) p ^ Dg.vDist p y = y ∧
      1 ≤ Dg.vDist p y ∧ Dg.vDist p y ≤ orderOf (S.orbitStep (S.twA κ) p) := by
  set σ := S.orbitStep (S.twA κ) p with hσ
  have hv : Dg.vPrev p y =
      basePoint σ y * σ ^ ((orbitPos σ y + orderOf σ - Dg.vDist p y) % orderOf σ) := rfl
  have hdv : Dg.vDist p y = prevV (orderOf σ) (topPositions Dg.TT σ (basePoint σ y)) (orbitPos σ y) := rfl
  obtain ⟨h1, h2, h3, h4⟩ := prevV_spec_of_ne_zero (hdv ▸ hd)
  rw [← hdv] at h1 h2 h3 h4
  have h3' := mem_filter.1 h3
  rw [hv]
  refine ⟨h3'.2, basePoint_basePoint_mul _ _ _, ?_, basePoint_mul_back _ _ h2, h1, h2⟩
  unfold IsVType
  rw [orbitPos_basePoint_mul _ _ (mem_range.1 h3'.1)]
  exact h4

/-- **The distance to the nearest V-top is odd** from a non-V top, when `ord σ_p` is even. -/
theorem odd_vDist {p : ℕ} (hn : Even (orderOf (S.orbitStep (S.twA κ) p))) {y : S.A} (hd : Dg.vDist p y ≠ 0)
    (hy : ¬ IsVType (S.orbitStep (S.twA κ) p) y) : Odd (Dg.vDist p y) := by
  obtain ⟨-, h2, -, h4⟩ := prevV_spec_of_ne_zero hd
  exact odd_of_back hn h2 hy h4

open scoped Classical in
/-- **L5, the V-top surplus** pays the depth's first term: at an inert `p` with `ord h_p` even,
`Σ_{non-V y} [d(y) ≠ 0]·min(b_y, a_{y′}/p^{d(y)}) ≤ Σ_{V-tops s} Σ_e g(s, e) + #(non-V tops)·(c₀ + 1)`. A term with
`d(y) ∉ gainExps` is `≤ 1` (L4, `d(y)` odd); one with `d(y) ∈ gainExps` is at most `g(y′, d(y)) + c₀`, as the
partner of `y′` at `d(y)` is the top `(1, y)`; and `y ↦ (y′, d(y))` is injective. -/
theorem dep0_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : p.Prime) (hin : S.cls p = .inert) (hev : Even (orderOf (S.hPtw (S.twA κ) p))) (t₀ : S.A) :
    (∑ y ∈ (Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y),
        if Dg.vDist p y = 0 then 0 else min (pr.bT y : ℝ) (Dg.a (Dg.vPrev p y) / (p : ℝ) ^ Dg.vDist p y)) ≤
      (∑ s ∈ (Dg.topsOn p t₀).filter (fun s => IsVType (S.orbitStep (S.twA κ) p) s),
          ∑ e ∈ gainExps x ε p, Dg.surplus u J p s e) +
        ((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card * (Dg.c0 + 1) := by
  have hp2 := hp.two_le
  have hσ : S.orbitStep (S.twA κ) p = S.hPtw (S.twA κ) p := by simp [Setting.orbitStep, hin]
  have hev' : Even (orderOf (S.orbitStep (S.twA κ) p)) := hσ ▸ hev
  have hc0 := Dg.c0_nonneg
  have hbx : 0 ≤ scB' x ε / x := div_nonneg (scB'_pos ε hA.big.pos).le hA.big.pos.le
  set σ := S.orbitStep (S.twA κ) p
  set N := (Dg.topsOn p t₀).filter (fun y => ¬ IsVType σ y)
  set V := (Dg.topsOn p t₀).filter (fun s => IsVType σ s)
  set E := gainExps x ε p
  set g : S.A × ℕ → ℝ := fun z => Dg.surplus u J p z.1 z.2
  set φ : S.A → S.A × ℕ := fun y => (Dg.vPrev p y, Dg.vDist p y) with hφ
  -- step 1: term by term
  have step1 : ∀ y ∈ N, (if Dg.vDist p y = 0 then 0 else
      min (pr.bT y : ℝ) (Dg.a (Dg.vPrev p y) / (p : ℝ) ^ Dg.vDist p y)) ≤
      (if Dg.vDist p y ≠ 0 ∧ Dg.vDist p y ∈ E then g (φ y) else 0) + (Dg.c0 + 1) := by
    intro y hy
    obtain ⟨hyT, hyV⟩ := mem_filter.1 hy
    have hyTT := (mem_filter.1 hyT).1
    by_cases hd : Dg.vDist p y = 0
    · rw [ite_eq_left hd, ite_eq_right (fun h => h.1 hd)]
      linarith
    rw [ite_eq_right hd]
    obtain ⟨hy'TT, -, -, hmul, hd1, -⟩ := Dg.vPrev_spec p hd
    have hodd := Dg.odd_vDist hev' hd hyV
    set d := Dg.vDist p y
    set y' := Dg.vPrev p y
    have hp0 : (0 : ℝ) < (p : ℝ) ^ d := pow_pos (by exact_mod_cast hp.pos) _
    by_cases hdE : d ∈ E
    · rw [ite_eq_left ⟨hd, hdE⟩]
      have hpos : S.pos (S.twA κ) p (1, y') d = (1, y) := by rw [Setting.pos_one_of_inert _ hin, hmul]
      have hw := (hA.top_window hF u J hyTT).1
      have h2c := Dg.two_c0_div_le hp2 hd1
      have hab : Dg.abar y' / (p : ℝ) ^ d = Dg.a y' / (p : ℝ) ^ d - 2 * Dg.c0 / (p : ℝ) ^ d := by
        unfold abar; rw [sub_div]
      have key : min (pr.bT y : ℝ) (Dg.a y' / (p : ℝ) ^ d) ≤ Dg.surplus u J p y' d + Dg.c0 := by
        unfold surplus
        rw [hpos, ← min_add_add_right]
        exact le_min (by linarith [min_le_right (pr.bT y : ℝ) (Dg.a y' / (p : ℝ) ^ d)])
          (by linarith [min_le_left (pr.bT y : ℝ) (Dg.a y' / (p : ℝ) ^ d)])
      have hgφ : g (φ y) = Dg.surplus u J p y' d := rfl
      linarith
    · rw [ite_eq_right (fun h => hdE h.2)]
      have hlt := lt_pow_of_notMem_gainExps hp2 hodd hdE
      have ha := hA.a_le_two hF hy'TT
      have h1 : Dg.a y' / (p : ℝ) ^ d ≤ 1 := (div_le_one hp0).2 (by linarith)
      linarith [min_le_right (pr.bT y : ℝ) (Dg.a y' / (p : ℝ) ^ d)]
  -- step 2: sum
  have step2 := sum_le_sum step1
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter] at step2
  -- step 3: the injection into `V × E`
  have hinj : Set.InjOn φ (N.filter fun y => Dg.vDist p y ≠ 0 ∧ Dg.vDist p y ∈ E) := by
    intro y₁ hy₁ y₂ hy₂ h
    have e₁ := (Dg.vPrev_spec p (mem_filter.1 hy₁).2.1).2.2.2.1
    have e₂ := (Dg.vPrev_spec p (mem_filter.1 hy₂).2.1).2.2.2.1
    simp only [hφ, Prod.mk.injEq] at h
    rw [← e₁, ← e₂, h.1, h.2]
  have hsub : (N.filter fun y => Dg.vDist p y ≠ 0 ∧ Dg.vDist p y ∈ E).image φ ⊆ V ×ˢ E := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hz
    obtain ⟨hyN, hd, hdE⟩ := mem_filter.1 hy
    obtain ⟨hyT, -⟩ := mem_filter.1 hyN
    obtain ⟨hy'TT, hb, hV', -⟩ := Dg.vPrev_spec p hd
    refine mem_product.2 ⟨mem_filter.2 ⟨mem_filter.2 ⟨hy'TT, ?_⟩, hV'⟩, hdE⟩
    rw [hb]
    exact (mem_filter.1 hyT).2
  have step3 : ∑ y ∈ N.filter (fun y => Dg.vDist p y ≠ 0 ∧ Dg.vDist p y ∈ E), g (φ y) ≤
      ∑ s ∈ V, ∑ e ∈ E, Dg.surplus u J p s e := by
    rw [← sum_image hinj, ← sum_product' (f := fun s e => Dg.surplus u J p s e)]
    refine sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => ?_
    obtain ⟨hz1, hz2⟩ := mem_product.1 hz
    exact Dg.surplus_nonneg hA hF u J hp2 (mem_filter.1 (mem_filter.1 hz1).1).1 (one_le_of_mem_gainExps hz2)
  linarith

/-! ## The per-orbit inequality -/

open scoped Classical in
/-- **The core of the per-orbit inequality**: `Σ_{tops} ask ≤ g^{sv} + sl − Σ_{V-tops} Σ_e g(s, e) +
#(non-V tops)·2c₀·|gainExps|` (L1 at the non-V tops, L2 at the V-tops). -/
theorem sum_askE_le (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : 2 ≤ p) (t₀ : S.A) :
    ∑ s ∈ Dg.topsOn p t₀, Dg.askE u J p s ≤ Dg.gSv u J p t₀ + Dg.sl p t₀ -
      (∑ s ∈ (Dg.topsOn p t₀).filter (fun s => IsVType (S.orbitStep (S.twA κ) p) s),
          ∑ e ∈ gainExps x ε p, Dg.surplus u J p s e) +
      ((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card *
        (2 * Dg.c0 * (gainExps x ε p).card) := by
  have key : ∀ s ∈ Dg.topsOn p t₀, Dg.askE u J p s +
      (if IsVType (S.orbitStep (S.twA κ) p) s then ∑ e ∈ gainExps x ε p, Dg.surplus u J p s e else 0) ≤
      (if IsVType (S.orbitStep (S.twA κ) p) s then gamP p * Dg.abar s
        else ∑ e ∈ gainExps x ε p, max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0) +
      (if ¬ IsVType (S.orbitStep (S.twA κ) p) s then 2 * Dg.c0 * (gainExps x ε p).card else 0) := by
    intro s hs
    by_cases hV : IsVType (S.orbitStep (S.twA κ) p) s
    · simp only [hV, ite_true, not_true_eq_false, ite_false, add_zero]
      linarith [Dg.askE_le_V hA hF u J hp (mem_filter.1 hs).1]
    · simp only [hV, ite_false, not_false_eq_true, ite_true, add_zero]
      exact Dg.askE_le_nonV u J hp s
  have h := sum_le_sum key
  rw [sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, nsmul_eq_mul] at h
  unfold gSv
  linarith

open scoped Classical in
/-- **The per-orbit inequality** (the gain spec §2.6, without goodness): on every orbit of tops at an inert `p` with
`ord h_p` even, `Σ_{tops} ask ≤ g^{sv} − pen − (⌈dep⌉ + D_p + 1) + sl + #tops·(2c₀·|gainExps| + topAllow) +
n_p·orbAllow`. The core (`sum_askE_le`) leaves `Σ_{V-tops} Σ_e g(s, e)`, which pays the depth's first term (L5,
`dep0_le`) for `p ≥ p₀`; the penalty's top terms are `≤ b′/x + η` each (the top window); the rest of `pen`, `dep`
and `D_p` is the allowance. -/
theorem orbit_ineq (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : p.Prime) (hin : S.cls p = .inert) (hev : Even (orderOf (S.hPtw (S.twA κ) p))) (t₀ : S.A) :
    ∑ s ∈ Dg.topsOn p t₀, Dg.askE u J p s ≤
      Dg.gSv u J p t₀ - Dg.pen pr u J p t₀ - ((⌈Dg.dep pr p t₀⌉₊ : ℝ) + Dg.Dexp p + 1) + Dg.sl p t₀ +
        (Dg.topsOn p t₀).card * (2 * Dg.c0 * (gainExps x ε p).card + Dg.topAllow p) +
        S.nP (S.twA κ) p * Dg.orbAllow p := by
  have hp2 := hp.two_le
  have hx := hA.one_le_x
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have ha1 := one_le_scA ε hx
  have ha0 : 0 ≤ scA x ε := by linarith
  have hlg : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p ha1
  have hδ : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0 _
  have hb' : 0 ≤ scB' x ε := (scB'_pos ε hA.big.pos).le
  have hbx : 0 ≤ scB' x ε / x := div_nonneg hb' hx0
  have hw'' : 0 ≤ scW'' S x ε := by unfold scW''; positivity
  have hLa : 0 ≤ scLa x ε Dg.R.k := by unfold scLa; have := Real.log_nonneg ha1; positivity
  have hc0 := Dg.c0_nonneg
  have heta := Dg.eta_nonneg
  have hk := Dg.one_le_k
  have hnp : (1 : ℝ) ≤ S.nP (S.twA κ) p := by exact_mod_cast S.one_le_nP _ p
  have hN1 : (1 : ℝ) ≤ Dg.R.N Dg.R.m := by exact_mod_cast Dg.one_le_N
  have core := Dg.sum_askE_le hA hF u J hp2 t₀
  have hVM : 0 ≤ ∑ s ∈ (Dg.topsOn p t₀).filter (fun s => IsVType (S.orbitStep (S.twA κ) p) s),
      ∑ e ∈ gainExps x ε p, Dg.surplus u J p s e :=
    sum_nonneg fun s hs => sum_nonneg fun e he =>
      Dg.surplus_nonneg hA hF u J hp2 (mem_filter.1 (mem_filter.1 hs).1).1 (one_le_of_mem_gainExps he)
  have hNT : (((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card : ℝ) ≤
      (Dg.topsOn p t₀).card := by exact_mod_cast card_filter_le _ _
  have hT0 : (0 : ℝ) ≤ (Dg.topsOn p t₀).card := Nat.cast_nonneg _
  by_cases hp0 : scP0 x Dg.R.k ≤ p
  · have hdep0 := Dg.dep0_le hA hF u J hp hin hev t₀
    have hcDep : 0 ≤ Dg.cDep p := by unfold cDep; positivity
    have hR : 0 ≤ Kg.cκ₁ * ((Dg.topsOn p t₀).card : ℝ) * (tilePar x ε Dg.R.k).N₁ *
          (scA x ε / (p : ℝ) ^ 2 + scLa x ε Dg.R.k * scA x ε / (p * Dg.R.k)) +
        Kg.cκ₂ * (Dg.topsOn p t₀).card * ((p : ℝ) ^ (tilePar x ε Dg.R.k).G' * Dg.cDep p +
          Dg.R.k * (p : ℝ) ^ (tilePar x ε Dg.R.k).G' + Dg.R.k * Real.logb p (scA x ε) + Dg.c0) +
        2 * S.nP (S.twA κ) p * Dg.c0 := by positivity
    have hdep : Dg.dep pr p t₀ ≤
        (∑ s ∈ (Dg.topsOn p t₀).filter (fun s => IsVType (S.orbitStep (S.twA κ) p) s),
          ∑ e ∈ gainExps x ε p, Dg.surplus u J p s e) +
        ((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card * (Dg.c0 + 1) +
        (Kg.cκ₁ * ((Dg.topsOn p t₀).card : ℝ) * (tilePar x ε Dg.R.k).N₁ *
          (scA x ε / (p : ℝ) ^ 2 + scLa x ε Dg.R.k * scA x ε / (p * Dg.R.k)) +
        Kg.cκ₂ * (Dg.topsOn p t₀).card * ((p : ℝ) ^ (tilePar x ε Dg.R.k).G' * Dg.cDep p +
          Dg.R.k * (p : ℝ) ^ (tilePar x ε Dg.R.k).G' + Dg.R.k * Real.logb p (scA x ε) + Dg.c0) +
        2 * S.nP (S.twA κ) p * Dg.c0) := by
      rw [dep, ite_eq_left hp0]
      linarith
    have hceil := natCeil_le_add_one hdep (by positivity)
    have hD : (Dg.Dexp p : ℝ) ≤ (Kg.cD₁ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε * x ^ 26 *
        (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 3) * Real.logb p (scA x ε) + 1 := by
      rw [Dexp, ite_eq_left hp0]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hpen : Dg.pen pr u J p t₀ ≤
        ((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card *
          (scB' x ε / x + Dg.eta) +
        Kg.cPr * S.nP (S.twA κ) p * (scW'' S x ε + Dg.eta + Dg.c0 + Dg.R.N Dg.R.m) := by
      rw [pen, ite_eq_left hp0]
      have h1 : ∑ s ∈ (Dg.topsOn p t₀).filter (fun s => ¬ IsVType (S.orbitStep (S.twA κ) p) s),
          (Dg.wsh u J (1, s) - pr.bT s) ≤
          ∑ s ∈ (Dg.topsOn p t₀).filter (fun s => ¬ IsVType (S.orbitStep (S.twA κ) p) s),
            (scB' x ε / x + Dg.eta) := by
        refine sum_le_sum fun s hs => ?_
        have h2 := (hA.top_window hF u J (mem_filter.1 (mem_filter.1 hs).1).1).2
        linarith [Dg.wsh_le_wt u J (1, s)]
      rw [sum_const, nsmul_eq_mul] at h1
      linarith
    have h1 : (((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card : ℝ) *
        (scB' x ε / x + Dg.eta + Dg.c0 + 1 + 2 * Dg.c0 * (gainExps x ε p).card) ≤
        (Dg.topsOn p t₀).card * (scB' x ε / x + Dg.eta + Dg.c0 + 1 + 2 * Dg.c0 * (gainExps x ε p).card) :=
      mul_le_mul_of_nonneg_right hNT (by positivity)
    rw [topAllow, ite_eq_left hp0, orbAllow, ite_eq_left hp0]
    linarith
  · have hdep : 0 ≤ Dg.dep pr p t₀ := by
      rw [dep, ite_eq_right hp0]
      positivity
    have hceil := natCeil_le_add_one le_rfl hdep
    have hD : (Dg.Dexp p : ℝ) ≤ (Kg.cD₂ : ℝ) * 40 * S.nP (S.twA κ) p * scδ₁ x ε *
        (((tilePar x ε Dg.R.k).N₁ : ℝ) ^ 3 + ((tilePar x ε Dg.R.k).r : ℝ) ^ 5 + (Dg.R.k : ℝ) ^ 2) *
          Real.logb p (scA x ε) + 2 * (tilePar x ε Dg.R.k).r * S.nP (S.twA κ) p * Dg.c0 +
        (tilePar x ε Dg.R.k).r * 40 * S.nP (S.twA κ) p * scδ₁ x ε * (2 * scB' x ε + 2 * Dg.c0) + 1 := by
      rw [Dexp, ite_eq_right hp0]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have h1 : (((Dg.topsOn p t₀).filter (fun y => ¬ IsVType (S.orbitStep (S.twA κ) p) y)).card : ℝ) *
        (2 * Dg.c0 * (gainExps x ε p).card) ≤ (Dg.topsOn p t₀).card * (2 * Dg.c0 * (gainExps x ε p).card) :=
      mul_le_mul_of_nonneg_right hNT (by positivity)
    have edep : Dg.dep pr p t₀ = Dg.dep pr p t₀ := rfl
    conv_rhs at edep => rw [dep, ite_eq_right hp0]
    rw [pen, ite_eq_right hp0]
    rw [topAllow, ite_eq_right hp0, orbAllow, ite_eq_right hp0]
    linarith

/-- **A collision costs no ask** at an inert `p ≥ X′`: the partner is a top `(1, y)`, of weight
`w ≥ b_y + b′/x ≥ b′(1 + 1/x) ≥ a_s/X′ ≥ a_s/p^e`. -/
theorem ask_term_eq_zero_of_collides (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A)
    (J : Fin Dg.R.m) {p : ℕ} (hX : scX' x ε ≤ p) {s : S.A} (hs : s ∈ Dg.TT) {e : ℕ} (he : 1 ≤ e)
    (hc : S.Collides (S.twA κ) p Dg.TT s e) :
    max (Dg.a s / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, s) e)) 0 = 0 := by
  obtain ⟨-, -, h1, h2⟩ := hc
  have hpos : S.pos (S.twA κ) p (1, s) e = (1, (S.pos (S.twA κ) p (1, s) e).2) := Prod.ext h1 rfl
  have hw := (hA.top_window hF u J h2).1
  have hb := (hF.bT_mem _ h2).1
  rw [← hpos] at hw
  have hX0 : 0 < scX' x ε := Real.exp_pos _
  have hp1 : (1 : ℝ) ≤ p := le_trans (by unfold scX'; exact Real.one_le_exp (Real.rpow_nonneg (by
    linarith [hA.one_le_x]) _)) hX
  have hpe : scX' x ε ≤ (p : ℝ) ^ e := hX.trans (le_self_pow₀ hp1 (by omega))
  have ha0 : 0 ≤ Dg.a s := by linarith [hA.two_c0_le_a hF hs, Dg.c0_nonneg]
  have ha := hA.a_le hF hs
  have h3 : Dg.a s / (p : ℝ) ^ e ≤ Dg.a s / scX' x ε := div_le_div_of_nonneg_left ha0 hX0 hpe
  have h4 : Dg.a s / scX' x ε ≤ scB' x ε + scB' x ε / x := by
    rw [div_le_iff₀ hX0]
    have : (scB' x ε + scB' x ε / x) * scX' x ε = scA x ε + scA x ε / x := by
      unfold scB'; field_simp
    linarith
  exact max_eq_right (by linarith)

open scoped Classical in
/-- **The per-orbit inequality, trivial-gain form**: at a signal `p`, or an inert `p ≥ X′`, `Σ_{tops} ask ≤ g^{tr} +
sl + #tops·2c₀·|gainExps|`. A collision costs no ask (none at a signal `p`; `ask_term_eq_zero_of_collides`), and the
other terms obey L1. -/
theorem orbit_ineq_tr (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (J : Fin Dg.R.m) {p : ℕ}
    (hp : p.Prime) (hcls : S.cls p = .signal ∨ (S.cls p = .inert ∧ scX' x ε ≤ p)) (t₀ : S.A) :
    ∑ s ∈ Dg.topsOn p t₀, Dg.askE u J p s ≤
      Dg.gTr u J p t₀ + Dg.sl p t₀ + (Dg.topsOn p t₀).card * (2 * Dg.c0 * (gainExps x ε p).card) := by
  have hp2 := hp.two_le
  have key : ∀ s ∈ Dg.topsOn p t₀, Dg.askE u J p s ≤
      ∑ e ∈ (gainExps x ε p).filter (fun e => ¬ S.Collides (S.twA κ) p Dg.TT s e),
        max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 + 2 * Dg.c0 * (gainExps x ε p).card := by
    intro s hs
    have hsT := (mem_filter.1 hs).1
    unfold askE
    rw [← sum_filter_add_sum_filter_not (gainExps x ε p) (fun e => S.Collides (S.twA κ) p Dg.TT s e)]
    have h0 : ∑ e ∈ (gainExps x ε p).filter (fun e => S.Collides (S.twA κ) p Dg.TT s e),
        max (Dg.a s / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, s) e)) 0 = 0 := by
      refine sum_eq_zero fun e he => ?_
      obtain ⟨heE, hc⟩ := mem_filter.1 he
      rcases hcls with hsig | ⟨-, hX⟩
      · exact absurd hc (Setting.not_collides_of_signal hsig _ _ _)
      · exact Dg.ask_term_eq_zero_of_collides hA hF u J hX hsT (one_le_of_mem_gainExps heE) hc
    rw [h0, zero_add]
    have h1 : ∑ e ∈ (gainExps x ε p).filter (fun e => ¬ S.Collides (S.twA κ) p Dg.TT s e),
        max (Dg.a s / (p : ℝ) ^ e - Dg.wt u J (S.pos (S.twA κ) p (1, s) e)) 0 ≤
        ∑ e ∈ (gainExps x ε p).filter (fun e => ¬ S.Collides (S.twA κ) p Dg.TT s e),
          (max (Dg.abar s / (p : ℝ) ^ e - Dg.cap u J p s e) 0 + 2 * Dg.c0) :=
      sum_le_sum fun e he => Dg.ask_term_le u J hp2 s (one_le_of_mem_gainExps (mem_filter.1 he).1)
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at h1
    have h2 : (((gainExps x ε p).filter (fun e => ¬ S.Collides (S.twA κ) p Dg.TT s e)).card : ℝ) ≤
        (gainExps x ε p).card := by exact_mod_cast card_filter_le _ _
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith [Dg.c0_nonneg] : (0 : ℝ) ≤ 2 * Dg.c0)
    linarith
  have h := sum_le_sum key
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at h
  unfold gTr
  linarith

/-! ## The gains against the asks -/

/-- **The orbits of the tops cover at most `2|A|` positions**: `#basePts·n_p ≤ 2|A|`, as `(t₀, i) ↦ t₀σ_p^i` is
injective on `basePts × [0, ord σ_p)` (base points are fixed, powers below the order distinct) and
`n_p ≤ 2·ord σ_p` (`n_p = 2·ord(h_p²)`, `σ_p = h_p²` at a signal `p`). -/
theorem card_basePts_mul_le (p : ℕ) :
    (Dg.basePts p).card * S.nP (S.twA κ) p ≤ 2 * Fintype.card S.A := by
  set σ := S.orbitStep (S.twA κ) p with hσ
  have h1 : (Dg.basePts p).card * orderOf σ ≤ Fintype.card S.A := by
    rw [← card_range (orderOf σ), ← card_product, ← card_univ]
    refine card_le_card_of_injOn (fun z => z.1 * σ ^ z.2) (fun _ _ => mem_coe.2 (mem_univ _)) ?_
    rintro ⟨t₀, i⟩ hz ⟨t₁, j⟩ hz' h
    obtain ⟨ht₀, hi⟩ := mem_product.1 (mem_coe.1 hz)
    obtain ⟨ht₁, hj⟩ := mem_product.1 (mem_coe.1 hz')
    simp only at h ht₀ ht₁ hi hj
    have hb : ∀ t ∈ Dg.basePts p, basePoint σ t = t := by
      intro t ht
      obtain ⟨t', -, rfl⟩ := mem_image.1 ht
      exact basePoint_basePoint _ _
    have e₀ : t₀ = t₁ := by
      have := congrArg (basePoint σ) h
      rwa [basePoint_mul_pow, basePoint_mul_pow, hb _ ht₀, hb _ ht₁] at this
    subst e₀
    rw [mul_right_inj] at h
    rw [pow_injOn_Iio_orderOf (mem_range.1 hi) (mem_range.1 hj) h]
  have h2 : S.nP (S.twA κ) p ≤ 2 * orderOf σ := by
    rw [hσ]
    unfold Setting.nP Setting.orbitStep
    split_ifs <;> omega
  calc (Dg.basePts p).card * S.nP (S.twA κ) p ≤ (Dg.basePts p).card * (2 * orderOf σ) :=
        Nat.mul_le_mul_left _ h2
    _ = 2 * ((Dg.basePts p).card * orderOf σ) := by ring
    _ ≤ 2 * Fintype.card S.A := Nat.mul_le_mul_left _ h1

/-- **The per-orbit allowance is nonnegative** for `x ≥ 1`. -/
theorem orbAllow_nonneg (hx : 1 ≤ x) (p : ℕ) : 0 ≤ Dg.orbAllow p := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlg : 0 ≤ Real.logb p (scA x ε) := logb_nat_nonneg p (one_le_scA ε hx)
  have hδ : 0 ≤ scδ₁ x ε := Real.rpow_nonneg hx0 _
  have hb' : 0 ≤ scB' x ε := (scB'_pos ε (by linarith)).le
  have hw'' : 0 ≤ scW'' S x ε := by unfold scW''; positivity
  have hc0 := Dg.c0_nonneg
  have heta := Dg.eta_nonneg
  unfold orbAllow
  split_ifs <;> positivity

/-- **`slack₂` is nonnegative** for `x ≥ 1`. -/
theorem slack2_nonneg (hx : 1 ≤ x) (p : ℕ) : 0 ≤ Dg.slack2 p := by
  have hlg : 0 ≤ Real.logb p (2 * scA x ε) := logb_nat_nonneg p (by linarith [one_le_scA ε hx])
  have := Dg.orbAllow_nonneg hx p
  unfold slack2
  split_ifs <;> positivity

/-- **The slacks of the orbits** sum to at most `c_{dl,1}·2|A|·N_m²·log_p(2a) + c_{dl,2}·|TT|·log_p(2a)²`, over
any set of base points (`card_basePts_mul_le`, and the orbits partition the tops). -/
theorem sum_sl_le (hx : 1 ≤ x) (p : ℕ) {P : Finset S.A} (hP : P ⊆ Dg.basePts p) :
    ∑ t₀ ∈ P, Dg.sl p t₀ ≤ Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
      Real.logb p (2 * scA x ε) + Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2 := by
  have hlg : 0 ≤ Real.logb p (2 * scA x ε) := logb_nat_nonneg p (by linarith [one_le_scA ε hx])
  have h1 : ∑ t₀ ∈ P, Dg.sl p t₀ ≤ ∑ t₀ ∈ Dg.basePts p, Dg.sl p t₀ :=
    sum_le_sum_of_subset_of_nonneg hP fun t₀ _ _ => Dg.sl_nonneg hx p t₀
  have hcard : ∑ t₀ ∈ Dg.basePts p, ((Dg.topsOn p t₀).card : ℝ) = Dg.TT.card := by
    have := Dg.sum_topsOn p (fun _ => (1 : ℝ))
    simpa using this
  have h2 : (((Dg.basePts p).card * S.nP (S.twA κ) p : ℕ) : ℝ) ≤ ((2 * Fintype.card S.A : ℕ) : ℝ) := by
    exact_mod_cast Dg.card_basePts_mul_le p
  push_cast at h2
  have h3 : ∑ t₀ ∈ Dg.basePts p, Dg.sl p t₀ = Kg.cdl₁ * ((Dg.basePts p).card * S.nP (S.twA κ) p) *
      (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
      Kg.cdl₂ * (∑ t₀ ∈ Dg.basePts p, ((Dg.topsOn p t₀).card : ℝ)) * Real.logb p (2 * scA x ε) ^ 2 := by
    unfold sl
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_mul, ← mul_sum]
    ring
  rw [h3, hcard] at h1
  have h4 : (Kg.cdl₁ : ℝ) * ((Dg.basePts p).card * S.nP (S.twA κ) p) * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
      Real.logb p (2 * scA x ε) ≤ Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 *
      Real.logb p (2 * scA x ε) := by
    gcongr
  linarith

/-- **The tops of the served orbits**: a sum over `{t ∈ TT : basePoint(t) ∈ S_p}` is the sum over the served
orbits of the sums over their tops. -/
theorem sum_filter_served {M : Type*} [AddCommMonoid M] (p : ℕ) (f : S.A → M) :
    ∑ t ∈ Dg.TT.filter (fun t => basePoint (S.orbitStep (S.twA κ) p) t ∈ Dg.served p), f t =
      ∑ t₀ ∈ Dg.served p, ∑ s ∈ Dg.topsOn p t₀, f s := by
  rw [← sum_fiberwise_of_maps_to (g := basePoint (S.orbitStep (S.twA κ) p)) (t := Dg.served p)
    (fun t ht => (mem_filter.1 ht).2)]
  refine sum_congr rfl fun t₀ ht₀ => sum_congr ?_ fun _ _ => rfl
  ext s
  simp only [topsOn, mem_filter]
  constructor
  · rintro ⟨⟨hs, -⟩, h⟩
    exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact ⟨⟨hs, h ▸ ht₀⟩, h⟩

/-- **No served orbits off the candidates.** -/
theorem served_eq_empty_of_not_cand {p : ℕ} (h : p ∉ S.cand κ x ε Dg.R.k) : Dg.served p = ∅ := by
  unfold served
  rw [ite_eq_right fun h' => h h'.1]

/-- **The gains cover the asks** at a prime `p` (the gain spec, §2.6, summed over the orbits and the lifts):
`Σ_j Σ_{covered tops} ask − m·#covered·slack₁ − m·slack₂ ≤ Σ_j G_j(p) − τ_p`. Off the inert and signal `p ≤ X″` of
even order nothing is covered and `G = τ = 0`; at a signal `p` or `p ≥ X′` every orbit is unserved and obeys
`orbit_ineq_tr`; at an inert `p < X′` the served orbits obey `orbit_ineq` and their depths make up `τ_p − e_p`, and
the unserved ones are dropped. The slacks and the per-orbit allowances sum over the orbits by
`card_basePts_mul_le`. -/
theorem gains_ge_ask (hA : Dg.Adm) {pr : DesignPar S} (hF : Dg.FamAt pr) (u : S.A) (p : ℕ) :
    ∑ J, ∑ t ∈ Dg.coveredTops p, Dg.askE u J p t - Dg.R.m * (Dg.coveredTops p).card * Dg.slack1 p -
      Dg.R.m * Dg.slack2 p ≤ ∑ J, Dg.gainG pr u J p - Dg.tau pr p := by
  classical
  have hx := hA.one_le_x
  have hm1 := hA.one_le_m
  have hsl2 := Dg.slack2_nonneg hx p
  have hG0 : 0 ≤ ∑ J, Dg.gainG pr u J p := sum_nonneg fun J _ => Dg.gainG_nonneg pr u J p
  have hempty : Dg.coveredTops p = ∅ → Dg.served p = ∅ →
      ∑ J, ∑ t ∈ Dg.coveredTops p, Dg.askE u J p t - Dg.R.m * (Dg.coveredTops p).card * Dg.slack1 p -
        Dg.R.m * Dg.slack2 p ≤ ∑ J, Dg.gainG pr u J p - Dg.tau pr p := by
    intro hc hs
    have ht : Dg.tau pr p = 0 := by
      unfold tau
      rw [hs]
      simp
    rw [hc, ht]
    simp only [sum_empty, sum_const_zero, card_empty, Nat.cast_zero, mul_zero, zero_mul, sub_zero, zero_sub]
    nlinarith
  by_cases h1 : p ∈ Setting.Ranks.inertPrimes (S := S) (S.cutX x ε) ∧ Even (orderOf (S.hPtw (S.twA κ) p))
  swap
  · refine hempty ?_ ?_
    · unfold coveredTops
      rw [ite_eq_right h1]
    · unfold served
      rw [ite_eq_right]
      rintro ⟨hc, hi⟩
      exact h1 ⟨hi, (mem_filter.1 hc).2.1⟩
  have hp := Setting.Ranks.prime_of_mem_inertPrimes h1.1
  have hns : S.cls p ≠ .split := (mem_filter.1 h1.1).2.2.2
  have hgain : ∀ J, Dg.gainG pr u J p = ∑ t₀ ∈ Dg.basePts p, if t₀ ∈ Dg.served p then
      max (Dg.gSv u J p t₀ - Dg.pen pr u J p t₀) (max (Dg.gTr u J p t₀) 0) else max (Dg.gTr u J p t₀) 0 := by
    intro J
    unfold gainG
    rw [ite_eq_left h1]
  by_cases h2 : S.cls p = .signal ∨ scX' x ε ≤ p
  · -- every orbit unserved: the trivial-gain form
    have hnc : p ∉ S.cand κ x ε Dg.R.k := by
      intro hc
      obtain ⟨hPR, -⟩ := mem_filter.1 hc
      obtain ⟨hr, -, hin, -⟩ := mem_filter.1 hPR
      rcases h2 with h2 | h2
      · rw [h2] at hin
        exact absurd hin (by decide)
      · exact absurd h2 (not_le.2 (Nat.lt_ceil.1 (mem_range.1 hr)))
    have hserved := Dg.served_eq_empty_of_not_cand hnc
    have hcov : Dg.coveredTops p = Dg.TT := by
      unfold coveredTops
      rw [ite_eq_left h1, ite_eq_left h2]
    have htau : Dg.tau pr p = 0 := by
      unfold tau
      rw [hserved]
      simp
    have hcls : S.cls p = .signal ∨ (S.cls p = .inert ∧ scX' x ε ≤ p) := by
      rcases h2 with h2 | h2
      · exact Or.inl h2
      · cases hc : S.cls p
        · exact absurd hc hns
        · exact Or.inl rfl
        · exact Or.inr ⟨rfl, h2⟩
    have key : ∀ J, ∑ t ∈ Dg.TT, Dg.askE u J p t ≤ Dg.gainG pr u J p +
        (Kg.cdl₁ * (2 * Fintype.card S.A) * (Dg.R.N Dg.R.m : ℝ) ^ 2 * Real.logb p (2 * scA x ε) +
          Kg.cdl₂ * Dg.TT.card * Real.logb p (2 * scA x ε) ^ 2) +
        Dg.TT.card * (2 * Dg.c0 * (gainExps x ε p).card) := by
      intro J
      rw [← Dg.sum_topsOn p, hgain J]
      have h3 := sum_le_sum fun t₀ (_ : t₀ ∈ Dg.basePts p) => Dg.orbit_ineq_tr hA hF u J hp hcls t₀
      rw [sum_add_distrib, sum_add_distrib, ← sum_mul] at h3
      have hcard : ∑ t₀ ∈ Dg.basePts p, ((Dg.topsOn p t₀).card : ℝ) = Dg.TT.card := by
        have := Dg.sum_topsOn p (fun _ => (1 : ℝ))
        simpa using this
      rw [hcard] at h3
      have h4 : ∑ t₀ ∈ Dg.basePts p, Dg.gTr u J p t₀ ≤ ∑ t₀ ∈ Dg.basePts p, (if t₀ ∈ Dg.served p then
          max (Dg.gSv u J p t₀ - Dg.pen pr u J p t₀) (max (Dg.gTr u J p t₀) 0)
          else max (Dg.gTr u J p t₀) 0) :=
        sum_le_sum fun t₀ _ => by rw [hserved, ite_eq_right (notMem_empty t₀)]; exact le_max_left _ _
      linarith [Dg.sum_sl_le hx p (subset_refl (Dg.basePts p))]
    have h3 := sum_le_sum fun J (_ : J ∈ univ) => key J
    rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      nsmul_eq_mul] at h3
    rw [hcov, htau, slack1, slack2, ite_eq_right hnc, ite_eq_right hnc]
    push_cast
    linarith
  -- an inert `p < X′`
  have hin : S.cls p = .inert := by
    cases hc : S.cls p
    · exact absurd hc hns
    · exact absurd (Or.inl hc) h2
    · rfl
  have hcov : Dg.coveredTops p =
      Dg.TT.filter fun t => basePoint (S.orbitStep (S.twA κ) p) t ∈ Dg.served p := by
    unfold coveredTops
    rw [ite_eq_left h1, ite_eq_right h2]
  by_cases hS : (Dg.served p).Nonempty
  swap
  · have hs : Dg.served p = ∅ := not_nonempty_iff_eq_empty.1 hS
    refine hempty ?_ hs
    rw [hcov, hs]
    simp
  obtain ⟨t₁, ht₁⟩ := hS
  have hcand : p ∈ S.cand κ x ε Dg.R.k := ((Dg.mem_served_iff).1 ht₁).1.1
  -- the per-lift inequality on the served orbits
  have key : ∀ J, ∑ t ∈ Dg.coveredTops p, Dg.askE u J p t ≤ Dg.gainG pr u J p +
      (-(∑ t₀ ∈ Dg.served p, ((⌈Dg.dep pr p t₀⌉₊ : ℝ) + Dg.Dexp p + 1)) +
        ∑ t₀ ∈ Dg.served p, Dg.sl p t₀ +
        (Dg.coveredTops p).card * (2 * Dg.c0 * (gainExps x ε p).card + Dg.topAllow p) +
        (Dg.served p).card * S.nP (S.twA κ) p * Dg.orbAllow p) := by
    intro J
    have hcard : ((Dg.coveredTops p).card : ℝ) = ∑ t₀ ∈ Dg.served p, ((Dg.topsOn p t₀).card : ℝ) := by
      rw [hcov]
      have := Dg.sum_filter_served p (fun _ => (1 : ℝ))
      simpa using this
    rw [hcov, Dg.sum_filter_served p, ← hcov, hcard]
    have h3 := sum_le_sum fun t₀ (_ : t₀ ∈ Dg.served p) => Dg.orbit_ineq hA hF u J hp hin h1.2 t₀
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_mul] at h3
    have h4 : ∑ t₀ ∈ Dg.served p, (Dg.gSv u J p t₀ - Dg.pen pr u J p t₀) ≤ Dg.gainG pr u J p := by
      rw [hgain J]
      calc ∑ t₀ ∈ Dg.served p, (Dg.gSv u J p t₀ - Dg.pen pr u J p t₀) ≤
          ∑ t₀ ∈ Dg.served p, (if t₀ ∈ Dg.served p then
            max (Dg.gSv u J p t₀ - Dg.pen pr u J p t₀) (max (Dg.gTr u J p t₀) 0)
            else max (Dg.gTr u J p t₀) 0) :=
            sum_le_sum fun t₀ ht₀ => by rw [ite_eq_left ht₀]; exact le_max_left _ _
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Dg.served_subset p) fun t₀ _ ht => by
            rw [ite_eq_right ht]
            exact le_max_right _ _
    rw [sum_sub_distrib] at h4
    have h5 : ∑ t₀ ∈ Dg.served p, ((⌈Dg.dep pr p t₀⌉₊ : ℝ) + Dg.Dexp p + 1) =
        ∑ t₀ ∈ Dg.served p, (⌈Dg.dep pr p t₀⌉₊ : ℝ) + (Dg.served p).card * (Dg.Dexp p : ℝ) +
          (Dg.served p).card * 1 := by
      rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    linarith
  have h3 := sum_le_sum fun J (_ : J ∈ univ) => key J
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have htau : (Dg.tau pr p : ℝ) = Dg.eSand p +
      Dg.R.m * ∑ t₀ ∈ Dg.served p, ((⌈Dg.dep pr p t₀⌉₊ : ℝ) + Dg.Dexp p + 1) := by
    unfold tau
    rw [ite_eq_left ⟨t₁, ht₁⟩]
    push_cast
    rw [mul_sum]
  have hS1 := Dg.sum_sl_le hx p (Dg.served_subset p)
  have hS2 : (((Dg.served p).card * S.nP (S.twA κ) p : ℕ) : ℝ) ≤ ((2 * Fintype.card S.A : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_right _ (card_le_card (Dg.served_subset p))).trans
      (Dg.card_basePts_mul_le p)
  push_cast at hS2
  have hor := Dg.orbAllow_nonneg hx p
  have he0 : (0 : ℝ) ≤ Dg.eSand p := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ Dg.R.m := by linarith
  have k1 := mul_le_mul_of_nonneg_left hS1 hm0
  have k2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS2 hor) hm0
  have k3 : (Dg.eSand p : ℝ) ≤ Dg.R.m * Dg.eSand p := le_mul_of_one_le_left he0 hm1
  rw [htau, slack1, slack2, ite_eq_left hcand, ite_eq_left hcand]
  nlinarith

end SharpDesign

end

end ZetaBalance
