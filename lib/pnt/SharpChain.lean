import SharpBound
import ThetaChain
import HermForms
import ThetaNorm
import ThetaVol
import RowSpace

/-!
# The sharp frontier with the theta chain — CONDITIONAL on the half-plane

Closes the chain hook of `SharpBound` (L7): the canonical hook `thetaHook`, whose `col` is the top of the theta chain
(`ThetaChain.Top.col` after `ThetaChain.Data.chain`), and the frontier `SharpBoundTheta := SharpBound thetaHook`.

**The reading** (`IsThetaCol`; spec-10 F4–F5, the archive's `colCpl`/`evGSD`). `col φ` is a function on the row
points `x` of the level (decorated lattices `pX x` of rank `n = N_m − 1`, `ST = ∅`, frames on `SG ∪ Q`), with
* (a) the chain read at the points: the chain has length `m = m2 + 2` and **no level `m`** (the archive's chain ends at
  level `m − 1`). Steps `j < m − 2` run between classes (`Data.chain`); level `m − 1` carries the coset `Y`, in its
  collapsed form `ȳ ∈ ∏_{P ∈ Q \ SG} (O/P^{m−1})^{N_{m−1}}` (spec-10 F5 item 5, redone for the representatives in
  `TwNF`: `ThetaVol.xiCpl`; pairs `(c, ȳ)` with the class's mass); step `m − 2` has the coupled factor `xiCpl` (`XiStd`
  at `SG`, `q^{−(m−1)N_{m−1}}·om(Φ_P)([x | ȳ_P])` at `Q`), and the top
  step maps `(c, ȳ)` straight to each point `x` through the lattice of its decorated lift `tilQ tz (pX x)`
  (`HermClasses.tilQ`: `til 1 N`, `f_P = tz·a mod P`, all frames kept), with its own determinant idele and Heisenberg
  data and the factor `xiTop` (`PhiTop·ftY`: `top` the first `N_m − 1` rows of `x′` in the point's frames, `η =
  conj(tz)⁻¹·x′_last`, as the archive). Every factor reads its matrix at `P` in the frames of the source and target
  (`HermClasses.inFr`, `ThetaChain.DecoF.frAt`: the archive's `inFr`, `frsF`) and carries the level-`T` indicator
  `HermClasses.phiT` (at the top with target
  the lift, so its `f_P = tz·a` is read). Then `col φ x = Θ_m(inp(e φ))(x)`
  (`Top.col`) at every point: no class representative of `[tilQ x]`, no transport, no character `χ_m` (the archive's
  `evRho` law is a consequence, not a datum);
* (b) the cast `N_m = n + 1` (`polCast`, `latCast`);
* (c) `inp`: forms → the chain's input, `F ↦ (c ↦ F(rep c))` with the lattice frames of `rep c` at `Q` forgotten
  (`Data.inp`, `DecoF.d`; the archive's `startC`, spec-11 §1), after an `L`-isomorphism `e` of the source
  with `X ⊓ V_ω` (`HermForms.Vω` at step 0, with the explicit level `uniUT` and a character over `lamGen`), for a
  cusp subspace `X` stable under the diamond operators (L7 notes, item 3; `X ≤ Forms` adds nothing to `X ⊓ V_ω`).
  `X`, `e` and the step-0 data (`ST`, `SG`, `n0`, `λ_0`, `χ0`) are chosen once per word and passed in, the same at
  every level (audit 7, T1a: the archive twists the lift characters, not the input form); each level's chain
  agrees with them (`D.ST = ST`, `D.SG = SG`, `D.n 0 = n0`, `D.lam 0 = λ_0`) and reads `e φ` through `fnCast`;
* (d) `Data` and its top `Top` existential, with `ChIdx`'s conditions on the fields `Data` has: the classes of every
  level, step 0 included, are classes of the archive's `DecoF` (`ThetaChain.DecoF`: residue frames on `SG`, lattice
  frames `fr_P`, `fr_P(O_(P)^n) = N_(P)`, at `P ∈ Q`; `D.Q = Q`; spec-11 A0, §1, spec-12 F6), `β 0` and `β(m−1)`
  singletons, every `β j` finite, `Λ 0 = uniUT` at `SG` and all of `GL_{N_0}(O_(P))` at `P ∈ Q`; its level data
  `(β, Λ)` are a `ChIdx`'s (`Λ = ChIdx.grp`, `S = ST ∪ SG ∪ Q`, `σ₀` of `P`), up to a bijection of the index types,
  with the groups and characters at `P ∈ Q` of the levels `1 ≤ j < m` pinned (`ThetaVol.LevQOk`, the archive's
  `grpQ`/`chrQ`: `prX(R1 ∩ h·JQ(k + j)·h⁻¹) ∩ GL(O_(P))` and `ψ_P(n1Arg r)⁻¹·ξ_P(det)⁻¹` on the `[k + j, N_j)` block;
  at `h = 1` the parahoric of `(k + j, j·t)`), and so are the groups at `SG` (`ThetaVol.LevGOk`, the archive's `grpG`:
  `∏_{w ∈ SG} red_w(prX(R1 ∩ JGsym_j))`, `h = 1` there) and their characters (the archive's `chrG` with its `chiInv`
  at `h = 1`, spec-13 F4–F5: `ḡ ↦ ∏_{w ∈ SG} ψ_w(n1Arg r_w)⁻¹·lamGS(entB(r_w))` for every family of lifts
  `r_w ∈ R1 ∩ JGsym_j` with `A(r_w)` reducing to `ḡ_w`, `ThetaVol.lamGS` the archive's `lamGvS`; read by no factor);
  distinct indices of a level have representatives in distinct double cosets `R1·h·JQ(k + j)` at some `P ∈ Q`
  (`ThetaVol.SameDC`, the archive's `inj`), so at the untwisted level, where `Q = ∅`, every `β j` is a subsingleton
  (the archive's one tuple); without these, copies of an index or a smaller level at `SG` would scale `col` by a
  positive integer per word (audit 11, T3a). Indices in one double coset at `P ∈ Q` have one representative there
  (the archive's `IdxProd`). Conversely no live double coset is dropped (the archive's `surj` at `Q`, spec-13 F1–F3,
  F7): for `j < m − 2` with `β j` nonempty, a `TwNF` tuple `hh` at level `j + 1` that is reached at every `P ∈ Q` by
  some `h_{j,b}`, `b` depending on `P`, with the step-`j` factor at `P` nonzero (`ThetaVol.XiStdAt`, the factor of
  `XiStd` at one place) is in `R1·h_{j+1,b′}(P)·JQ(k + j + 1)` for one `b′` at every `P ∈ Q`; with `inj` and the
  nonvanishing clause below, `β(j + 1)` is then the product over `Q` of the live double cosets at each place (the
  archive's `twNext`; spec-13 F8). Without it, a choice of a live-closed subset of the double cosets would change
  `col`. Its characters are `μ_{0,j}ξ`
  with `μ_{0,j}` a `LiftChars` for given `e`, `Sg`, equal to the family `mu0` passed in (the pinned frontier shares it
  across levels and words and reads it in the rows).
  At every level, the representatives are `h_{j,b}(P) = 1` at `P ∈ SG` (the archive's `twIdx`, spec-7 §2b), in the
  archive's normal form `TwNF` at `P ∈ Q` (never integral at the live levels, spec-12 F3–F5), and the
  local factors are pinned at every coset: `Ξ_j`, `j < m − 2`, by `ThetaVol.XiFull` over the row set `SG ∪ Q` (spec-3
  §1, spec-6, spec-7 §3, spec-10 F5 item 1): `Ξ_j = ∏_P volN_P⁻¹·E1(om(Φ_P))`; the two top factors by `xiCpl` and
  `xiTop` (spec-10 F5 item 5); with the representatives `h` the same `ChIdx`'s, the
  canonical sharp instance (`J = JGsym`, `Φ_P = PhiGS ∘ entB` at `SG`; `JQ(k + j)`, `Φ_P = PhiQ ∘ entB` at `Q`
  (`phQ`); depth `m + 1`, `N_j = k + j(t + 1)`), and `ψ_P`, `μ_P`, `χ_P`, `√q` existential with the canonical
  properties for `μ_{0,j}` and the twist `ξ` (`ThetaVol.LocOk`, `dQ = 2m`; `√q` one per place, the same at every
  step). `Q` (a parameter) is `sel(Qprime ξ)`:
  one place over each place where `ξ` ramifies (as a pair `{P, P̄}`), never both `P` and `P̄`, of prime norm and
  unramified over `ℚ` (spec-7 §3a; `Q = ∅` when `U`), off `tz` and `conj(tz)` (spec-11 §3: `N P ≠ T_ω`, the
  archive's `PosT`; the frame of the lift `tilQ` at `P ∈ Q` divides by `conj(tz)`), and off `SG` and `conj SG` (the
  archive's `QSep`; so `sel` can hold `SG ∪ Q` with one place of each pair).
  Against `κ ≡ 0`: `S = ST ∪ SG ∪ Q` (the archive's place set `Sall` of `homAt`, spec-8 F2b; `ST ∪ SG` when `U`),
  `cA, cB > 0`, the Heisenberg data (the top step's too) have
  `SA, SB ≠ ∅` and `vol > 0`, and every class at a level `j + 1 ≤ m − 2` meets a nonzero `Ξ` (the archive's `nonvan`,
  `i < m2`; at `j = m − 2` the factor at `Q` is a Fourier transform in `ȳ`, spec-10 F3).
* (e) Normalisation (audit 3, B1): the determinant ideles (L5.2, `IsDetIdele`) follow the archive's `muOff` (spec-5 §4,
  spec-8 F2): for a set `sel` (existential) holding one place of each conjugate pair `v ≠ conj v`, every self-conjugate
  place, and the frame places `SG ∪ Q`, they have the valuation of `det N_c` (the largest `v(det f)`, `f ∈ N_c^n`) at
  the places of `sel`, and component `1` at the others (the conjugates of `sel`, those of `SG ∪ Q` included), at every
  level and over every split place, not only over `ST`; at each frame place `P` of the class (or point; `SG ∪ Q` at
  every level) the component is
  `det fr_P` (`DecoF.frAt`; the archive's `muInvDet`; the unit part is pinned there); the top step's is that of the
  lift `tilQ tz (pX
  x)`, whose frames cover `SG ∪ Q` (spec-10 F4). When `U` (the untwisted level): `ξ = 1` (spec-2 4a). At every level the
  chain's `ST`, `SG` are the given ones. The Heisenberg data are pinned (`Data.XDPinned`, spec-3 §3, spec-5 §3;
  `Top.XDPinned` at the top step): `HA = halfAO` with `c = cA·cB`, `BC = ι(halfBO)` with `c = cB`, `SA`, `SB`
  representatives (`IsReps`, `0 ∈ SA`), `vol = volS`. The base theta of every step `j < m` is normalised
  (`ThetaStd.Normalised`) by a canonical pin (`ThetaNorm.Pin.Canonical`: `Lc = δ·φ₀(cc)` with `Δ(Lc) = 1`, `s =
  1/area(Lc)`, `σ = σ*_{Lc}`, `Λ = ι(𝔄)`), so its scale is fixed up to a phase. One pin is passed in (`pin`) and
  shared by every step, every chain of the translate, all words and all levels (`thetaHook`), so the phase `κ` is one
  per translate (audit 13, T2 (i)): a `κ` chosen per chain, with only `|κ| = 1`, could be `σ₀(γ)`, `γ = x/star x ∈ L`,
  of any `w`-adic valuation. This is the archive's `Base` exactly: one per column datum, with no level, word or step
  index (its `κ` = `KapChoice.kappa`, fixed by `γ₀` and the per-prime data; the step enters only through the ranks
  of `tensPow`, and every field of `Pin` is rank-free; caveats-1, Q2); spec-4's `Lc`, `σ`, `Λ` depend only on the base
  lattice.

**The pinned frontier** (`SharpBoundPinned`) adds what the hook cannot see: the chain's CM type is `τ_K`, the
branching maps are `PeriodTarget.br` with `c_Br = brConst ≠ 0` and `IsFockProj` at `λ = λ_m` and
`σ = P.σ = sgT` of `hc u` (`BrPinned`, `lamW`, `sgW`; `λ_m` per word, of the word's HC family `hcW ω`, the archive's
`hcW u`, equal to `hc u` in `v`, `b`, `e`, `u_0`, `u_{k−1}`), the lift characters have `e_j` of `hc u` and `Sg` the
places above `g₀g₁` (`eW`, `Sg`),
`(−d/g₀) = (−d/g₁) = 1`, and
`T_ω = ππ̄` with `π = (a + b√−d)/2 ≡ 1 (mod M)`, `M = QS·q·d·(g₀g₁)²` (`SharpData.Arith`; for `d ≡ 3 (mod 4)`,
`π − 1 ∈ M·O_{K₀}` iff `M ∣ b` and `a ≡ b + 2 (mod 2M)`). It implies `SharpBoundTheta`.

**Source pins** (L4.3, L6.5, audit of `KLattice.G`): through each word's `e` (the one every level reads), the pinned
frontier takes `K` normal over `ℚ` with a star (not CM: the archive's `K` contains `j(cc)`), `M_ω` the `O_K`-span of
the integral forms `HermForms.Mω` of `X ⊓ V_ω`, and the source metric at `v` the complex Petersson form
`H_{ω,σ_v}` (`HermForms.petAt`: `σ_v` on the coefficients, then the Fock form over `ℂ`; the archive's metric at every
place), in the coordinates of the frame (`KFrame.RealisesPet`). Not `σ_v(H_ω)` with the star of `K`: that is hermitian
only where the star is conjugation, and depends on the basis elsewhere (the two agree where the star is conjugation,
`HermForms.petAt_eq_map`). The target metric stays existential. Every level's `X`, `lsh`, `V0` are pinned by one
clause on `SG ∪ QE μ` with `ST = ∅` (spec-7 §2c, spec-9; "Rows" below). Not pinned: a lower bound on `X` or on the
words.

**Rows** (spec-9; `RowSpace`). At every level `μ` (`QE μ0 = ∅`): `G μ ≃* Grp E n (SG ∪ QE μ) Λ_μ` and `X μ ≃ points Λ_μ`
with `ST = ∅`, compatibly, `Λ_μ = rowLevel SG (QE μ)` (`HKJ` at `SG`: block upper triangular for `(r, t, …, t)` with the
`r × r` block `I`; `HQ` at `QE μ`: the parabolic `(r, m·t)`), finitely many classes, `lsh = N`, the same points as the
chain's (`IsThetaCol`'s `pX`; its top step maps to their lifts `tilQ tz`, on the chains' `ST`), and `V0_μ` the class
functions `c ↦ φ(rep c)` of `φ ∈ V0pt = idemOf X (Amb ⊓ AmbPt)`: `AmbPt` the `VV(σ)`-valued `φ` on points with `φ((γ,
h)·x) = rowChar(h)·ρ_σ(γ)φ(x)`, `rowChar`
the residues at `SG` of the lift characters `mu0 s` on the `t`-block determinants and at `QE μ` of the twist `ξT μ` on
the `m·t`-block determinant; `Amb` the `(Psym, ψ)`-isotypic part for the type group `𝔊 = ∏_{w ∈ SG} GL_r(O_E/w)`, `r = k
+ m − 1`, acting through the Levi block `diag(a, I)` (`levi`, `tyRep`), with `Psym = ∏ HPsymF_w` and `j ∘ ψ = chiSym
xi0` (`ψ₀(Σ_{i ≠ k−1} u_{i,i+1})`); `X` one nonempty set of irreducible characters of `𝔊` for all levels (not
`Gal`-stable: the archive's need not be). The lift characters `mu0` are every chain's (`IsThetaCol`'s `Cμ.mu`).

**Untwisted level, `tz`, `𝔞`** (L2.3, L2.5, L6.5; audit 2, A4–A5). At `μ0` the level is the decorated lattices: `G μ0 ≃*
Grp E n SG Λ` and `X μ0 ≃ points Λ` with no `ST` decorations (`ST = ∅`), compatibly with the actions (`n = N_m − 1`),
with `lsh μ0 x` the lattice `N` of the point, and the chains map to its lift `tilQ x` (unimodular lattices, which
cannot be rescaled); its level is `rowLevel SG ∅` ("Rows"). As at every level (spec-8 F4), the archive's row points
are `DecoSet(N_m − 1, ∅, SG ∪
QE)` with integrality from `∇_N`, not `Lsh`; `ST` enters only through the chains' `D.ST`, at rank `N_m` (`tilQ`). `ST`,
`SG` are every level's chains' `D.ST`, `D.SG` (`IsThetaCol`, `U := μ = μ0`): `ST` the places over `π_T = conj(tz)`, `SG`
half the places over `g₀g₁` (each in `SG` or in `conj SG`, not both). At every level the chain shape is pinned
(`SharpData.Shp`: `m = R.m`, `n_j = N_j`, `e_j` of `hc u`, `λ_j` of the word's `hcW ω`, `cA = (∏_{SG ∪ Q} N P)^{m+1}`,
`cB = T_ω·cA`, `sd = √d/2`), so the per-level pins over `j < m` bind at the twisted levels too. `tz = (a + bs)/2`
with `s² = −d` and `(a, b)` as in `SharpData.Arith` for `T_ω`, at every word: `tz ∈ {π, π̄}` (the root `s` is not
tied to the CM type). `tz` and `ST` are per word (`PerData.tz ω`), as in the archive, which chooses `T` and its prime
per word (`Pr.T u`, `Pr.piT u`), so the words of `u` may have different `T_ω` (the archive's `T` lies in a window
`Tstar ≤ T ≤ (1 + 1/(fk))·Tstar` read off the word's own `ColumnsAtT`). `𝔞_ω` is fractional, `𝔞⁺(𝔞⁻)⁻¹` with
integral `𝔞⁺`, `𝔞⁻` (`PeriodTarget.Nsrc`): the archive's `𝔞_ω⁻¹ = Iu` has negative exponents where `sg(ω, w) < 0`,
over `T_ω` and the primes of `DGam` above `X″` (verify C8), so an integral `𝔞_ω` could never shrink `N_ω` below
`M_ω`. It is not the archive's `Iu⁻¹` (the local weights `sg(ω, w)` are not defined here) but is capped on both sides:
`𝔞⁺ ∣ aBd u ω` and `𝔞⁻ ∣ aBdN u ω`, parameter-defined integers, so it can neither raise nor lower `μ(N_ω)` without
limit.

**Open.** Existential: `Data`'s remaining fields (theta constants, `Ξ` before the last step, weights, `ξ` at the
twisted levels, `dI` up to units at the places of `sel` off the frame places, the side `sel` picked over each pair off
`SG ∪ Q`, the top step's Heisenberg representatives), `N(cc)` in `xi0`, `X`, `e` (one per word, shared by every
level), `𝔞⁺, 𝔞⁻` below caps, the untwisted level's `ST`, `SG`, the branching projection, the `ChIdx` representatives at
`Q` (one per double coset, in `TwNF`). Every level's classes carry lattice frames at `Q` (the archive's `DecoF`), so
every factor reads `x` at `P ∈ Q` in the frames without ambiguity; residue frames would not do, as the representatives
there are in `TwNF`, not integral (spec-12 F6). The live `ν ≤ −1` of `TwNF` (spec-12 F5) is not pinned (redundant
given the nonvanishing clause; audit 12). The archive's `int` (`prCat ≤ GLint`) needs no pin: at `Q` it follows from
`TwNF` (the archive's `NF` and its `prCat_le_GLint`), at `SG` from `h = 1` and `JGsym ≤ stabL(lamY)` (audit 12, T1,
T4). Not stated: `Tw` by the archive's `TwistedSetDef` (the untwisted kernel indices `Ij`, `jw` and per-place forced
orders are not defined here), the `SG` clause of the archive's `surj` (its `twSurjG`: at `w ∈ SG`, a `g ∈
stabL(lamY)` reached from `1` with `E1` not identically `0` is in `R1·JGsym_{j+1}`; with `h = 1` there it is a closed
statement about the canonical local objects, independent of the index, so it pins no choice; spec-13 F7),
`ψ_w`'s offset avoidance (`IsTwist`, `AvoidSet`), and `GoodTw`'s index bound (on the step-`j` theta image lattices,
which the frontier does not reach: "Twist characters" below). `surj` at `Q` asks `TwNF` and
a nonzero `XiStdAt` at depth `m + 1`, where the archive asks `TwBdd` and `E1` not identically `0` at all large depths
(`FiniteSumNonzeroLargeDepth`): the Lean hypothesis is never weaker (`TwNF` implies `TwBdd`; `XiStdAt ≠ 0` gives `E1 ≠
0` at depth `m + 1`, where the archive's `E1` has stabilised), so the clause is implied by the archive's (spec-13 F3,
F8).

**Twist characters** (spec-7 §1c–1d, `SharpData.RealisedPinned`). Each level `μ` has a twist `ξ_μ` (`ξT`, read by
`IsThetaCol` through `Shp`), `1` at `μ0` and `δ_ℓ·ψ_w` at `μ(w) ≠ μ0`, `ℓ` the residue characteristic of `w`: `δ_ℓ` is
`δ` (`Hecke.IsDelta pde`), or `δ′` (`IsDelta pde′`) when `ℓ = pde`, with `pde ≠ pde′` existential primes `≠ T_ω` (so
`δ_ℓ` never ramifies over `ℓ`: audit 8, C1); `ψ_w` is `Hecke.IsPsi ℓ Q_w`. Of the archive's `GoodTw` only a finiteness
is kept, at `μ(w)`: for every word, the `w`-integral sources `A_ω = {φ ∈ V_ω : P_{μ(w)}(φ)(R_{μ(w)}) ⊆ O_w}` and `B_ω =
{φ ∈ V_ω : P_{μ0}(φ)(R_{μ0}) ⊆ O_w}` have `[A_ω + B_ω : B_ω]` finite (at `w`). It holds for the archive's objects
(`adm1`: `ker P_{μ(w)} = ker P_{μ0}` on the sources, `ze` a `w`-unit), and with `C_u` a lattice (`KFrame.tgt`) it forces
the twisted periods to have full rank on `W_u`. The archive's spanning (`IsLatIn`) is not stated otherwise: stated
dually (the periods separate `V0_{μ(w)}`) it is not provable (audit 8, S2).

**The index bound of `GoodTw` is not stated** (caveats-1). The archive's bound, `Σ_{j,b} ε_{j,b} ≤ ℓ⁻²`, is on the
step-`j` theta image lattices, per lift step `j ∈ [1, m]` and side `b` (the two conjugate embeddings: `w` and `w̄`),
against a level-independent reference lattice of the step-`j` space, which the twisted and untwisted chains share; its
period-side use (`ONTw`) bounds the per-lift kernel indices at `μ(w)`, with forced terms besides the `2/ℓ²`. The
frontier does not reach those lattices: only step 0 (`V_ω`, through the shared `e`) is common to the levels, and each
level's step-`j` outputs live on the classes of its own existential `Data`. The former stand-in, a joint bound `Σ_ω
log[A_ω : B_ω] ≤ ℓ⁻²` on the last step's sources at every conjugate `ψ_w^a`, is not implied by the archive's bound
(duality gives neither the split over the words nor image ↔ row-dual), so it could make the frontier false; dropping it
keeps the frontier true. It stays sharp: no free non-unit scalar is left on the twisted columns (the shared `e`, audit 8
T1a; the shared pin, audit 13; `ze` a unit; `Shp`, `TwNF` and `XiFull` at every level), the dropped clause was one-sided
anyway (it never blocked a larger twisted image, audit 8 S4), and `ψ_w` is an arithmetic choice, not a tunable scalar.
**Unchecked:** whether a choice of `Q_w` (places with `N P ≡ 1 mod ℓ^K`) can put an `ℓ`-adic non-unit into the twisted
local volumes (the `volN` indices at `Q`, `ThetaVol`).

**Sanity theorem:** `Data.comp_zero_inp`.
-/

namespace ZetaBalance

open NumberField IsDedekindDomain HermClasses ThetaChain WeylFock

noncomputable section

section Hook

variable {Φ : Type} [Fintype Φ] [DecidableEq Φ] {E L : Type} [Field E] [NumberField E] [IsCMField E] [Field L]
  [NumberField L] {τ : Φ → (E →+* L)}

/-- (b) The cast `N = N′` of a polynomial (the chain's `N_m` to `n + 1`). -/
def polCast {N N' : ℕ} (h : N = N') : Pol Φ N L → Pol Φ N' L := by
  subst h; exact id

/-- (b) The cast `N = N′` of a decorated lattice (the lift's `n + 1` to the chain's `N_m`). -/
def decoCast {N N' : ℕ} {ST SF : Finset (HeightOneSpectrum (𝓞 E))} (h : N = N') :
    Deco E N ST SF → Deco E N' ST SF := by
  subst h; exact id

/-- (c) Forms on the place sets `ST`, `SG` at step-0 rank `n0`, read at equal ones: a word's source data are shared by
every level, and each level's chain `D` has `D.ST = ST`, `D.SG = SG`, `D.n 0 = n0` (`IsThetaCol`). -/
def fnCast {ST ST' SG SG' : Finset (HeightOneSpectrum (𝓞 E))} {n0 n0' : ℕ} (h1 : ST = ST') (h2 : SG = SG')
    (h3 : n0 = n0') : HermForms.Fn ST (uniUT SG n0) Φ L →ₗ[L] HermForms.Fn ST' (uniUT SG' n0') Φ L := by
  subst h1 h2 h3; exact LinearMap.id

/-- (c) The chain's input from functions on decorated lattices with frames on `SG`: `F ↦ (c ↦ F(rep c))` on the step-0
classes, after forgetting the lattice frames of `rep c` at `Q` (spec-11 §1, the archive's `startC`: `φ ↦ (p ↦
φ(p.deco))`). -/
def _root_.ThetaChain.Data.inp (D : Data τ) (Λ : Subgroup (∀ w : D.SG, GL (Fin (D.n 0)) (𝓞 E ⧸ w.1.asIdeal))) :
    HermForms.Fn D.ST Λ Φ L →ₗ[L] (D.chain.C 0 → Pol Φ (D.n 0) L) :=
  LinearMap.funLeft L _ fun c =>
    ⟨c.2.rep.d, c.2.good.1⟩

omit [NumberField L] in
/-- **Sanity:** the chain of length `0` reads a form at the representative of each class, its frames at `Q`
forgotten. -/
theorem _root_.ThetaChain.Data.comp_zero_inp (D : Data τ)
    (Λ : Subgroup (∀ w : D.SG, GL (Fin (D.n 0)) (𝓞 E ⧸ w.1.asIdeal))) (F : HermForms.Fn D.ST Λ Φ L)
    (c : D.chain.C 0) :
    D.chain.comp 0 (D.inp Λ F) c =
      F ⟨c.2.rep.d, c.2.good.1⟩ :=
  rfl

/-- The archive's `IsDelta p` (spec-7 §1c, spec-2 4a): `δ` is of finite order, tame, unramified away from the
places over the auxiliary prime `p`, and of order exactly `15` on the local units at each of them. The twist
characters of `SharpData.RealisedPinned` are `δ_ℓ·ψ`, with `δ` at `pde` (`δ′` at `pde′` when `ℓ = pde`). -/
def _root_.ThetaChain.Hecke.IsDelta (p : ℕ) (δ : Hecke E L) : Prop :=
  (∃ k, 0 < k ∧ ∀ x, δ.toHom x ^ k = 1) ∧ δ.Tame Set.univ ∧ δ.UnramAway {v | (p : 𝓞 E) ∈ v.asIdeal} ∧
    ∀ v : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ v.asIdeal → ∀ k : ℕ,
      (∀ x ∈ unitsAway {w | w ≠ v}, δ.toHom x ^ k = 1) ↔ 15 ∣ k

/-- The archive's `IsPsi ℓ Q` (spec-7 §1c, spec-2 4a): `ψ` is of `ℓ`-power order, tame, ramified exactly at the
places of `Q` (nontrivial on the local units there and only there), each split (`v ≠ v̄`), and trivial on `E_v^×` at
every place `v` over `ℓ`. The `ℓ`-part of a twist character, `SharpData.RealisedPinned`. -/
def _root_.ThetaChain.Hecke.IsPsi (ℓ : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) (ψ : Hecke E L) : Prop :=
  (∃ k, ∀ x, ψ.toHom x ^ ℓ ^ k = 1) ∧ ψ.Tame Set.univ ∧
    (∀ v, (∃ x ∈ unitsAway {w | w ≠ v}, ψ.toHom x ≠ 1) ↔ v ∈ Q) ∧
    (∀ v ∈ Q, v.asIdeal ≠ v.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) ∧
    ∀ v : HeightOneSpectrum (𝓞 E), (ℓ : 𝓞 E) ∈ v.asIdeal → ∀ x : Ideles E,
      (∀ w ≠ v, (x : FiniteAdeleRing (𝓞 E) E) w = 1) → ψ.toHom x = 1

/-- (e) `dI` is a determinant idele of a lattice `N` with frames `fr` (L5.2; the archive's `muOff` and `muInvDet`,
spec-5 §4, spec-8 F2): at the places of `sel` it has the valuation of `det N` (the largest `v(det f)`, `f ∈ N^a`),
its component is `1` at the others (the archive's `muOff`: the component, not only the valuation, so no free unit
phase at the conjugates of `sel`), and at each frame place `P ∈ SF` its component is `det fr_P` (`fr_P(O_P^a) = N_P`,
so the valuation is that of `det N`): the unit part too is read through the frames. The frames are those the factors
read: of a class, `ThetaChain.DecoF.frAt` (frame lifts at `SG`, lattice frames at `Q`); of the lift at the top,
`HermClasses.frAt`. -/
def IsDetIdele (sel : Set (HeightOneSpectrum (𝓞 E))) {a : ℕ} (N : Submodule (𝓞 E) (Fin a → E))
    (SF : Finset (HeightOneSpectrum (𝓞 E))) (fr : HeightOneSpectrum (𝓞 E) → Matrix (Fin a) (Fin a) E)
    (dI : Ideles E) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 E), let dv := Valued.v (((dI : Ideles E) : FiniteAdeleRing (𝓞 E) E) v)
    (v ∈ sel → (∃ f : Fin a → N, dv = v.valuation E (Matrix.of fun i k => (f k : Fin a → E) i).det) ∧
      ∀ f : Fin a → N, v.valuation E (Matrix.of fun i k => (f k : Fin a → E) i).det ≤ dv) ∧
    (v ∉ sel → ((dI : Ideles E) : FiniteAdeleRing (𝓞 E) E) v = 1)) ∧
  ∀ P ∈ SF, ((dI : Ideles E) : FiniteAdeleRing (𝓞 E) E) P = algebraMap E (P.adicCompletion E) (fr P).det

open Classical in
/-- **`col` is the theta chain's** at one level and word, on the row points `x ∈ Xr` (decorated lattices `pX x` of rank
`n = N_m − 1` with `ST = ∅` and frames on `SG ∪ Q`): `col φ x = Θ_m(inp(e φ))(x)`, the top of a chain of length
`m = m2 + 2` (`ThetaChain.Top.col`, the archive's `colCpl`) at the decorated lift `tilQ tz (pX x)` of the point, for
theta data `D` with `ChIdx`'s conditions, the anti-degeneracy and normalisation conditions (at every level, the
`ChIdx` representatives `h_{j,b}(P)` in `GL(O_(P))` off `Q`, entrywise through `intAt` on `h` and `h⁻¹`; `U`: the
untwisted level) (module docstring, (a)–(e)). **The representatives at `P ∈ Q`** are in the archive's normal form
(`ThetaVol.TwNF`; `twRep`): `h·O^{N_j+c_j} = {v : v_{<N_j} − v_{N_j}·z ∈ O^{N_j}, v_{N_j+i} ∈ q^{ν_i}O}` with
`z ∈ O^{N_j}` and `−j ≤ ν_i ≤ 0`, i.e. `h ∈ n_z·diag(1, q^ν)·GL(O_(P))` (`h = 1` at `j = 0` and `j = m − 1`, `ChIdx`).
They are never integral at the live levels: at `ξ_P ≠ 1` the free last column of `E1` kills every integral coset,
and the `ψ_P` twist at denominator `q^{−1}` pairs with `ξ_P` into a Gauss sum (spec-12 F3–F5: the live `ν` have every
`ν_i ≤ −1` at `1 ≤ j ≤ m − 2`, `(−1, …, −1)` at `j = 1`; not pinned). An integrality pin at `Q` would keep only dead
cosets and make the frontier false at the twisted levels. The archive's `int` (`prCat ≤ GLint`) is implied, not
pinned: at `Q` by `TwNF` (the archive's `NF`, `prCat_le_GLint`), at `SG` by `h = 1`. **The index types and the
levels at `SG`** are pinned (audit 11, T3a; audit 12): distinct `b ≠ b′` at a level `j` have
`h_{j,b′}(P) ∉ R1·h_{j,b}(P)·JQ(k + j)` at some `P ∈ Q` (`ThetaVol.SameDC`, the archive's `inj`; at the untwisted
level, `Q = ∅`, every `β j` is a subsingleton); `b`, `b′` in one double coset at `P ∈ Q` have
`h_{j,b}(P) = h_{j,b′}(P)` (the archive's `IdxProd`); conversely (the archive's `surj` at `Q`, the source index chosen
per place; spec-13 F7), for `j < m − 2` with `β j` nonempty, every `hh` in `TwNF` at level `j + 1` such that at each
`P ∈ Q` some `h_{j,b}`, `b` depending on `P`, reaches `hh P` with `XiStdAt_P(x) ≠ 0` for some `x`
(`ThetaVol.XiStdAt`, the step-`j` factor at one place) is in `R1·h_{j+1,b′}(P)·JQ(k + j + 1)` for one `b′` at every
`P ∈ Q`; and at `1 ≤ j < m` the level group at `SG` is `∏_w red_w(prX(R1 ∩ JGsym_j))` (`ThetaVol.LevGOk`), with the
character `ḡ ↦ ∏_w ψ_w(n1Arg r_w)⁻¹·lamGS_w(entB(r_w))` for every family of lifts `r_w ∈ R1 ∩ JGsym_j` with
`IsRed(A(r_w), ḡ_w)` (the archive's `chrG` at `h = 1`; `ThetaVol.lamGS`, its `lamGvS`; `ψ`, `χ` those of
`LocOk`). The word's source data are passed in, the
same at every level (audit 7, T1a: the archive twists the characters, not the input form): the place sets `ST`, `SG`,
the step-0 rank `n0`, weight `lam0` and character `χ0`, a cusp subspace `X` stable under the diamond operators, and
an isomorphism `e` of the source with `X ⊓ V_ω`. The chain has `D.ST = ST`, `D.SG = SG`, `D.n 0 = n0`,
`D.lam 0 = lam0`, and reads `e φ` through `fnCast`. **The pin** of the base thetas is passed in too, one for every
step (`pin`, of form `s`; `ThetaNorm.Pin.Canonical`, `ThetaStd.Normalised`; the archive's `Base` has no step index),
so the caller can share it across the words and levels of a translate (audit 13: the phase `κ` is not free per
chain). `Shp D m Q ξ` is a further condition
on the data, length, `Q`
and twist `ξ`, set by the caller (the pinned frontier: the chain shape, `sd`, through `SharpData.RealisedPinned`).
**The star** of the coefficient field `L` is complex conjugation at the chain's embedding:
`σ₀ ∘ star = conj ∘ σ₀`, `σ₀ = D.P.σ₀` (the archive's `Fields.Ok`). `L` need not be CM: the archive's coefficient
field contains `j(cc)`, of odd degree `h(−d) ≥ 3` with a non-real embedding, so lies in no CM field. -/
def IsThetaCol [StarRing L] (τ : Φ → (E →+* L)) (eF : ℕ → Φ → ℤ) (Sg : Set (HeightOneSpectrum (𝓞 E))) (n : ℕ)
    (U : Prop) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (Q : Finset (HeightOneSpectrum (𝓞 E))) (xi0 : E)
    (mu0 : ℕ → Hecke E L) {s : ℝ} (pin : ThetaNorm.Pin Φ s)
    (Shp : Data τ → ℕ → Finset (HeightOneSpectrum (𝓞 E)) → Hecke E L → Prop) (tz : 𝓞 E) {Xr : Type}
    (pX : Xr → Deco E n ∅ (SG ∪ Q)) {V : Type}
    [AddCommGroup V] [Module L V] {n0 : ℕ} {lam0 : Φ → Fin n0 → ℤ} {χ0 : uniUT SG n0 →* L}
    {X : Submodule L (HermForms.Fn ST (uniUT SG n0) Φ L)} (e : V ≃ₗ[L] ↥(X ⊓ HermForms.Vω ST τ χ0 lam0))
    (col : V →ₗ[L] PeriodTarget.Col Φ n L Xr) : Prop :=
  ∃ (D : Data τ) (hST : D.ST = ST) (hSG : D.SG = SG) (h0 : D.n 0 = n0) (m2 : ℕ) (hm : D.n (m2 + 2) = n + 1)
    (Cμ : LiftChars τ (m2 + 2) eF Sg) (ξ : Hecke E L)
    (Tp : Top D m2 (SG ∪ Q) (∀ P : ↥(Q \ D.SG), Fin (D.n (m2 + 1)) → 𝓞 E ⧸ P.1.asIdeal ^ (m2 + 1)) Xr),
    Cμ.mu = mu0 ∧ (Nonempty (Unique (D.β 0)) ∧ Nonempty (Unique (D.β (m2 + 1))) ∧ (∀ j, Finite (D.β j)) ∧
      D.Q = Q ∧ (∀ b, D.Λ 0 b = (uniUT D.SG (D.n 0)).prod ⊤) ∧
      (∀ ρ i, D.lam 0 ρ i = lam0 ρ (Fin.cast h0 i)) ∧ (∀ x, D.P.σ₀ (star x) = starRingEnd ℂ (D.P.σ₀ x)) ∧
      ∀ g, D.P.σ₀ (χ0 g) = lamGen xi0 (g : ∀ w : SG, GL (Fin n0) (𝓞 E ⧸ w.1.asIdeal))) ∧
    (D.S = ↑D.ST ∪ ↑D.SG ∪ ↑Q ∧ (∀ j, 0 < D.cA j ∧ 0 < D.cB j) ∧
      (∀ j c c', (D.XD j c c').SA.Nonempty ∧ (D.XD j c c').SB.Nonempty ∧ 0 < (D.XD j c c').vol) ∧ D.XDPinned ∧
      (∀ c x, (Tp.XD c x).SA.Nonempty ∧ (Tp.XD c x).SB.Nonempty ∧ 0 < (Tp.XD c x).vol) ∧ Tp.XDPinned ∧
      ∀ j < m2, ∀ c', ∃ c x, D.Xi j c c' x ≠ 0) ∧
    (∃ (C : ChIdx D.SG D.Q D.n (m2 + 2) (D.ST ∪ D.SG ∪ Q) xi0 D.P.σ₀) (eβ : ∀ j, C.β j ≃ D.β j),
      (∀ j b, D.Λ j (eβ j b) = C.grp j b) ∧
      (∀ j b (Pl : ↥(D.ST ∪ D.SG ∪ Q)), Pl.1 ∈ D.SG → C.h j b Pl = 1) ∧
      (∀ j b (Pl : ↥(D.ST ∪ D.SG ∪ Q)), Pl.1 ∉ Q → ∀ a a', ThetaVol.intAt Pl.1 ((C.h j b Pl).val a a') ∧
          ThetaVol.intAt Pl.1 ((C.h j b Pl).inv a a')) ∧
      (∀ j b (Pl : ↥(D.ST ∪ D.SG ∪ Q)), Pl.1 ∈ Q →
        ThetaVol.TwNF (D.n j) (m2 + 2 - 1 - j) Pl.1 j (C.h j b Pl)) ∧
      ∃ (k t : ℕ) (χ ψ μ : ℕ → HeightOneSpectrum (𝓞 E) → E → L) (sq : HeightOneSpectrum (𝓞 E) → L),
        (∀ j, D.n j = k + j * (t + 1)) ∧
        (∀ j, ThetaVol.LocOk D.P.σ₀ xi0 (2 * (m2 + 2)) (D.SG ∪ Q) D.SG (Cμ.mu j).toHom ξ.toHom (ψ j) (μ j) sq
          (χ j)) ∧
        let h : ∀ j, D.β j → HeightOneSpectrum (𝓞 E) → GL (Fin (D.n j + (m2 + 2 - 1 - j))) E :=
          fun j b Pl => if hP : Pl ∈ D.ST ∪ D.SG ∪ Q then C.h j ((eβ j).symm b) ⟨Pl, hP⟩ else 1
        have hm' : D.n (m2 + 1 + 1) - 1 = n := by rw [show m2 + 1 + 1 = m2 + 2 from rfl, hm, Nat.add_sub_cancel]
        let Ph : ∀ j, HeightOneSpectrum (𝓞 E) →
            Matrix (Fin (D.n (j + 1) + (m2 + 2 - 1 - (j + 1)))) (Fin (D.n j + (m2 + 2 - 1 - j))) E → L :=
          fun j Pl => if Pl ∈ D.SG then ThetaVol.phS D (m2 + 2) k t ψ χ j Pl else ThetaVol.phQ D (m2 + 2) k χ j Pl
        (∀ j b (w : D.Q), 0 < j → j < m2 + 2 →
          ThetaVol.LevQOk (D.n j) (m2 + 2 - 1 - j) w.1 (k + j) (h j (eβ j b) w.1) (ψ j w.1) (χ j w.1)
            (C.levQ j b w) (C.chrQ j b w)) ∧
        (∀ j b, 0 < j → j < m2 + 2 →
          ThetaVol.LevGOk (D.n j) (m2 + 2 - 1 - j) (ThetaVol.jS D (m2 + 2) k t j) (C.Λ j b)) ∧
        (∀ j b, 0 < j → j < m2 + 2 → ∀ (g : C.Λ j b) (r : D.SG → GL (Fin (D.n j + (m2 + 2 - 1 - j))) E),
          (∀ w, r w ∈ ThetaVol.R1 (D.n j) (m2 + 2 - 1 - j) ⊓ ThetaVol.jS D (m2 + 2) k t j w.1 ∧
            ThetaVol.IsRed w.1 (ThetaVol.blkA (r w)) (g.1 w).1) →
          ((C.chr j b g : Lˣ) : L) = ∏ w : D.SG, (ψ j w.1 (ThetaVol.n1Arg (r w)))⁻¹ *
            ThetaVol.lamGS w.1 (ψ j w.1) (fun l => χ l w.1) k (k + (m2 + 2) - 1) t j
              (ThetaVol.entB w.1 k (D.n j) (D.n j) (m2 + 2 - 1 - j) (m2 + 2 - 1 - j) (fun i => i + 1) (r w).1)) ∧
        (∀ j (b b' : D.β j), b ≠ b' → ∃ w : D.Q, ¬ ThetaVol.SameDC (D.n j) (m2 + 2 - 1 - j)
          (ThetaVol.JQ (D.n j) (m2 + 2 - 1 - j) w.1 (k + j)) (h j b w.1) (h j b' w.1)) ∧
        (∀ j (b b' : D.β j) (w : D.Q), ThetaVol.SameDC (D.n j) (m2 + 2 - 1 - j)
          (ThetaVol.JQ (D.n j) (m2 + 2 - 1 - j) w.1 (k + j)) (h j b w.1) (h j b' w.1) → h j b w.1 = h j b' w.1) ∧
        (∀ j < m2, Nonempty (D.β j) →
          ∀ hh : HeightOneSpectrum (𝓞 E) → GL (Fin (D.n (j + 1) + (m2 + 2 - 1 - (j + 1)))) E,
          (∀ P ∈ Q, ThetaVol.TwNF (D.n (j + 1)) (m2 + 2 - 1 - (j + 1)) P (j + 1) (hh P)) →
          (∀ P ∈ Q, ∃ (b : D.β j) (x : Matrix (Fin (D.n (j + 1))) (Fin (D.n j)) E),
            ThetaVol.XiStdAt (D.n j) (D.n (j + 1)) (m2 + 2 - 1 - j) (m2 + 2 - 1 - (j + 1)) (m2 + 3) D.SG
              (ThetaVol.jS D (m2 + 2) k t (j + 1) P) (k + (j + 1)) (h j b P) (hh P) (ψ j P) (μ j P) (sq P) (Ph j P) P
              x ≠ 0) →
          ∃ b' : D.β (j + 1), ∀ w : D.Q, ThetaVol.SameDC (D.n (j + 1)) (m2 + 2 - 1 - (j + 1))
            (ThetaVol.JQ (D.n (j + 1)) (m2 + 2 - 1 - (j + 1)) w.1 (k + (j + 1))) (h (j + 1) b' w.1) (hh w.1)) ∧
        ThetaVol.XiFull D (m2 + 2) (m2 + 3) k (D.SG ∪ Q) h (ThetaVol.jS D (m2 + 2) k t) ψ μ (fun _ => sq) Ph ∧
          (∀ c₀ c y, Tp.Xi1 c₀ c y =
            ThetaVol.xiCpl D (m2 + 2) (m2 + 3) k (Q \ D.SG) h (ThetaVol.jS D (m2 + 2) k t) ψ μ (fun _ => sq)
              Ph m2 c₀ c y) ∧
          ∀ c y x, Tp.Xi2 c y x = ThetaVol.xiTop D (m2 + 2) k t (Q \ D.SG) ψ χ (m2 + 1) c (Tp.pt x)
            (fun P => (frAt (pX x) P).submatrix (Fin.cast hm') (Fin.cast hm'))
            (IsCMField.complexConj E (tz : E)) y) ∧
    ((U → ∀ x, ξ.toHom x = 1) ∧ ∀ j < m2 + 2, ∀ x, (D.mu j).toHom x = (Cμ.mu j).toHom x * ξ.toHom x) ∧
    (∀ v : HeightOneSpectrum (𝓞 E),
      (∃ P ∈ Q, P = v ∨ P.asIdeal = v.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) ↔
        ∃ x ∈ unitsAway {w | w ≠ v ∧
          w.asIdeal ≠ v.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)}, ξ.toHom x ≠ 1) ∧
    (∀ P ∈ Q, ∀ P' ∈ Q, P'.asIdeal ≠ P.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) ∧
    (∀ P ∈ Q, (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧
      tz ∉ P.asIdeal ∧ IsCMField.ringOfIntegersComplexConj E tz ∉ P.asIdeal ∧ P ∉ SG ∧
      ∀ w ∈ SG, P.asIdeal ≠ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) ∧
    Shp D (m2 + 2) Q ξ ∧
    (∀ j < m2 + 2, ThetaNorm.Pin.Canonical τ D.P pin ∧ (D.θ j).Normalised pin) ∧
    (∃ sel : Set (HeightOneSpectrum (𝓞 E)), ↑(D.SG ∪ Q) ⊆ sel ∧ (∀ v v' : HeightOneSpectrum (𝓞 E),
        v'.asIdeal = v.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E) →
          (v ∈ sel ↔ v = v' ∨ v' ∉ sel)) ∧
      (∀ j < m2 + 2, ∀ c : Cls D.n D.ST D.SG D.Q D.β D.Λ j, IsDetIdele sel c.2.N (D.SG ∪ Q) c.2.rep.frAt (D.dI j c)) ∧
      ∀ x, IsDetIdele sel (Tp.pt x).N (D.SG ∪ Q) (frAt (Tp.pt x)) (Tp.dI x)) ∧
    (∀ a, ∀ F ∈ X, HermForms.dOp a F ∈ X) ∧
    (∀ x, Tp.pt x = decoCast hm.symm (tilQ (ST := D.ST) tz (pX x))) ∧
    ∀ φ x, col φ x = polCast hm (Tp.col (D.chain.comp m2 (D.inp _ (fnCast hST.symm hSG.symm h0.symm (e φ).1))) x)

end Hook

-- CHAIN HOOK, closed: the canonical hook.
open Classical in
/-- **The theta hook**: at every level `μ`, the points `X μ` are decorated row points of rank `n` (through `pX`, with
`ST = ∅` and frames on `SG ∪ Q`), and `col μ ω` is the theta chain's (`IsThetaCol`: the top step maps to the lift
`tilQ tz` of each point) at every word `ω`, for a CM structure on `E`, a CM type `τ` and a coefficient field `L` as in
the archive's `Fields.Ok` (normal over `ℚ`, totally complex, with a star that `IsThetaCol` makes complex conjugation at
the chain's `σ₀`; not CM), with `SG` and the base theta's pin (one for every step, so one phase `κ`: audit 13; the
archive's `Base`) shared by the words and levels, and each word's `ST`, `tz` (its own auxiliary prime `T_ω`, as the
archive's per-word `Pr.T u`, `Pr.piT u`) and source data (`n0`, `lam0`, `χ0`, `X`, `e`) chosen once, outside the
level (audit 7, T1a). -/
def thetaHook : ChainHook := fun Φ _ _ n E L _ _ _ T Ω X Vs _ _ col =>
  ∃ (_ : IsCMField E) (_ : NumberField L) (_ : IsTotallyComplex L) (_ : Normal ℚ L) (_ : StarRing L)
    (τ : Φ → (E →+* L)) (eF : ℕ → Φ → ℤ)
    (Sg : Set (HeightOneSpectrum (𝓞 E))) (SG : Finset (HeightOneSpectrum (𝓞 E))) (s : ℝ)
    (pin : ThetaNorm.Pin Φ s),
    ∀ ω : Ω, ∃ (ST : Finset (HeightOneSpectrum (𝓞 E))) (tz : 𝓞 E) (n0 : ℕ) (lam0 : Φ → Fin n0 → ℤ)
      (χ0 : uniUT SG n0 →* L)
      (Xc : Submodule L (HermForms.Fn ST (uniUT SG n0) Φ L)) (e : Vs ω ≃ₗ[L] ↥(Xc ⊓ HermForms.Vω ST τ χ0 lam0)),
      ∀ μ : T, ∃ (U : Prop) (Q : Finset (HeightOneSpectrum (𝓞 E))) (xi0 : E)
        (mu0 : ℕ → Hecke E L) (Shp : Data τ → ℕ → Finset (HeightOneSpectrum (𝓞 E)) → Hecke E L → Prop)
        (pX : X μ → Deco E n ∅ (SG ∪ Q)),
        IsThetaCol τ eF Sg n U Q xi0 mu0 pin Shp tz pX e (col μ ω)

/-- **The sharp frontier with the theta chain**: `SharpBound` at the canonical hook. -/
def SharpBoundTheta : Prop := SharpBound thetaHook

/-- **CONDITIONAL. RH and GRH from `SharpBoundTheta`** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_sharpBoundTheta (h : SharpBoundTheta) : HalfPlaneGRH.RHandGRH := rhAndGRH_of_sharpBound h

/-! ## The pinned frontier -/

/-- **The branching maps are pinned** at weights `λ_ω` (per word: the archive's words have their own HC parameters
`hcW u`) and `σ`: the rows' weight is `P.σ = σ`, and `br ω = PeriodTarget.br τ tz_ω Π_σ c_Br λ_ω σ` with `Π_σ` the
Fock
projection (`IsFockProj`) and `c_Br` the closed form `PeriodTarget.brConst λ_ω σ` (spec-5 §1), nonzero; a closed form
of the word's weights, so no free scalar can rescale one word's period against another's. -/
def BrPinned {Φ : Type} [Fintype Φ] [DecidableEq Φ] {n : ℕ} {E L : Type} [Field E] [NumberField E] [Field L]
    (τ : Φ → (E →+* L)) {T Ω : Type} {G X : T → Type} [∀ μ, Group (G μ)] [∀ μ, MulAction (G μ) (X μ)]
    {Vs : Ω → Type} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module L (Vs ω)]
    (P : PeriodTarget.PerData Φ n E L G X Vs)
    (lam : Ω → Φ → Fin (n + 1) → ℤ) (σ : Φ → Fin n → ℤ) : Prop :=
  P.σ = σ ∧ ∀ ω, PeriodTarget.brConst L (lam ω) σ ≠ 0 ∧ ∃ Pr : Pol Φ n L →ₗ[L] Pol Φ n L,
    PeriodTarget.IsFockProj σ Pr ∧
      P.br ω = PeriodTarget.br τ (P.tz ω) Pr (PeriodTarget.brConst L (lam ω) σ) (lam ω) σ

section Pet

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {n : ℕ}
  {E : Type*} [Field E] [NumberField E] (τ : Φ → (E →+* K)) {T : Type*} {G X : T → Type*} [∀ μ, Group (G μ)]
  [∀ μ, MulAction (G μ) (X μ)]

open Classical in
/-- **Realised, with the source metrics pinned** (L4.3, L6.5): `KFrame.Realises`, and in the same coordinates `e ω`
as the lattices and the maps, the metric of `N_ω` at `v` is the Gram matrix of the form `hV ω σ_v` at the place's
embedding (in the pinned frontier, the complex Petersson form `H_{ω,σ_v}` of `X ⊓ V_ω`, `HermForms.petAt`,
`IsThetaCol`): `G_v(i, j) = hV_{σ_v}(e⁻¹δ_i, e⁻¹δ_j)`, as in `HermForms.gram` and `HermForms.source_G`. -/
def KFrame.RealisesPet (F : KFrame K) {Vs : F.ι → Type*} [∀ ω, AddCommGroup (Vs ω)] [∀ ω, Module K (Vs ω)]
    [∀ ω, Module (𝓞 K) (Vs ω)] [∀ ω, IsScalarTower (𝓞 K) K (Vs ω)]
    (D : PeriodTarget.PerData Φ n E K G X Vs) (μ0 : T) (tw : PeriodTarget.Twist D μ0)
    (𝔞p 𝔞n : F.ι → Ideal (𝓞 K)) (M : ∀ ω, Submodule (𝓞 K) (Vs ω)) (hV : ∀ ω, (K →+* ℂ) → Vs ω → Vs ω → ℂ) :
    Prop :=
  tw.IsTransfer ∧ (∀ w ∉ tw.Tw, tw.μw w = μ0) ∧ (∀ ω, 𝔞p ω ≠ ⊥ ∧ 𝔞n ω ≠ ⊥) ∧
    ∃ (e : ∀ ω, Vs ω ≃ₗ[K] (F.n ω → K)) (eC : (D.V0 μ0 → K) →ₗ[K] (F.κ → K)), Set.InjOn eC (D.W μ0) ∧
      (∀ ω, (F.src ω).M =
        (PeriodTarget.Nsrc τ tw 𝔞p 𝔞n M ω).map (((e ω : Vs ω →ₗ[K] (F.n ω → K))).restrictScalars (𝓞 K))) ∧
      F.tgt.M = (PeriodTarget.Ctgt τ tw).map (eC.restrictScalars (𝓞 K)) ∧
      (∀ ω φ, eC (D.P μ0 ω φ) = F.B ω (e ω φ)) ∧
      ∀ ω v i j, (F.src ω).G v i j = hV ω v.1.embedding ((e ω).symm (Pi.single i 1)) ((e ω).symm (Pi.single j 1))

omit [NumberField E] in
/-- **Sanity:** realised with the metrics pinned is realised. -/
theorem KFrame.RealisesPet.realises {F : KFrame K} {Vs : F.ι → Type*} [∀ ω, AddCommGroup (Vs ω)]
    [∀ ω, Module K (Vs ω)] [∀ ω, Module (𝓞 K) (Vs ω)] [∀ ω, IsScalarTower (𝓞 K) K (Vs ω)]
    {D : PeriodTarget.PerData Φ n E K G X Vs} {μ0 : T} {tw : PeriodTarget.Twist D μ0}
    {𝔞p 𝔞n : F.ι → Ideal (𝓞 K)} {M : ∀ ω, Submodule (𝓞 K) (Vs ω)} {hV : ∀ ω, (K →+* ℂ) → Vs ω → Vs ω → ℂ}
    (h : F.RealisesPet τ D μ0 tw 𝔞p 𝔞n M hV) :
    F.Realises τ D μ0 tw 𝔞p 𝔞n M := by
  obtain ⟨h1, h2, h3, e, eC, h4, h5, h6, h7, -⟩ := h
  exact ⟨h1, h2, h3, e, eC, h4, h5, h6, h7⟩

end Pet

variable {S : Setting} {κ : S.A →* ℂˣ} {x ε X : ℝ} {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

/-- A `Fin k`-indexed parameter read on `ℕ` (`0` from `k` on). -/
def finN {k : ℕ} (f : Fin k → ℤ) (j : ℕ) : ℤ := if h : j < k then f ⟨j, h⟩ else 0

/-- **The branching weight** of `u`: `σ = sgT(v, b, e)` of the HC parameters `hc u`, at rank `n = N_m − 1` (L6.1). -/
def SharpData.sgW (D : SharpData S κ x ε X K) (u : S.A) : Φ S.A → Fin (D.R.N D.R.m - 1) → ℤ :=
  PeriodTarget.sgT D.R.k D.R.t D.R.m (fun ρ => finN (D.hc u ρ).v) (fun ρ => finN (D.hc u ρ).b)
    (fun ρ => finN (D.hc u ρ).e)

theorem SharpData.N_sub_one_add_one (D : SharpData S κ x ε X K) :
    D.R.N D.R.m - 1 + 1 = D.R.k + D.R.m * (D.R.t + 1) := by
  have := D.R.m_add_three_le
  unfold Setting.Ranks.N
  omega

/-- The rank `r = k + m − 1` of the type group `∏_{w ∈ SG} GL_r(O_E/w)` (spec-9 item 2): `N_m − 1 = r + m·t`. -/
def SharpData.rr (D : SharpData S κ x ε X K) : ℕ := D.R.k + D.R.m - 1

theorem SharpData.rr_le (D : SharpData S κ x ε X K) : D.rr ≤ D.R.N D.R.m - 1 := by
  have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold SharpData.rr Setting.Ranks.N
  omega

/-- The weights `e_j` of `hc u`, for the lift characters (`LiftChars`). -/
def SharpData.eW (D : SharpData S κ x ε X K) (u : S.A) : ℕ → Φ S.A → ℤ := fun j ρ => finN (D.hc u ρ).e j

/-- The places of `E` above `g₀g₁`, where the lift characters may ramify (tamely). -/
def SharpData.Sg (D : SharpData S κ x ε X K) : Set (HeightOneSpectrum (𝓞 S.E)) :=
  {v | ((D.g₀ * D.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal}

/-- **The weight `λ_m`** of a word with HC family `hw` (`WeylFock.wt` at `j = m`, with `u_i − ½` and `e_j` of `hw`;
in `RealisedPinned` the word's `hcW ω`), read at rank `N_m = (N_m − 1) + 1`. -/
def SharpData.lamW (D : SharpData S κ x ε X K) (hw : D.R.HCFamily) : Φ S.A → Fin (D.R.N D.R.m - 1 + 1) → ℤ :=
  fun ρ i => WeylFock.wt D.R.k D.R.t D.R.m (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
    (Fin.cast D.N_sub_one_add_one i)

/-- **The arithmetic of the parameters** (L7.2): `(−d/g₀) = (−d/g₁) = 1`, and `T_ω = ππ̄` with
`π = (a + b√−d)/2 ≡ 1 (mod M)`, `M = QS·q·d·(g₀g₁)²`: `4T_ω = a² + db²`, `M ∣ b`, `a ≡ b + 2 (mod 2M)`. -/
def SharpData.Arith (D : SharpData S κ x ε X K) : Prop :=
  jacobiSym (-(S.d : ℤ)) D.g₀ = 1 ∧ jacobiSym (-(S.d : ℤ)) D.g₁ = 1 ∧
    ∀ u ω, ∃ a b : ℤ, 4 * (D.T u ω : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
      ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
      a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ)]

/-- The size of the HC parameters of `u`: `k + m + t` plus the absolute values of `u`, `v`, `b`, `e` over `Φ`. -/
def SharpData.wB (D : SharpData S κ x ε X K) (u : S.A) : ℕ :=
  D.R.k + D.R.m + D.R.t + ∑ ρ, ((∑ i, ⌈|(D.hc u ρ).u i|⌉₊) + (∑ i, ((D.hc u ρ).v i).natAbs) +
    ∑ j, (((D.hc u ρ).b j).natAbs + ((D.hc u ρ).e j).natAbs))

/-- **A cap for the positive part `𝔞⁺` of `𝔞_ω = 𝔞⁺(𝔞⁻)⁻¹`** (L6.5, a bound in place of the archive's
`𝔞_ω = Iu⁻¹ = ∏_{w∈supp}𝔓_w^{⌊e_w sg(ω,w)⌋}`, whose local weights `sg(ω, w)` are not defined here):
`(T_ω·d·g₀g₁·∏_{p ≤ X″} p)^{[K:ℚ]·N_m·wB(u)}`. Its prime factors cover the archive's support of `sg > 0` (`d`,
`g₀g₁`, the primes up to `X″`; `T_ω` generously); the exponent is a generous parameter bound, the same as `aBdN`'s.
The factor `N_m` (audit 13): the positive `Σ_j F_j` at `p = 2` reaches `(2/3)(k − 1)·wB`, which `[K:ℚ]·wB` covers only
when `[K:ℚ] ≳ k`, and `N_m ≥ k`. -/
def SharpData.aBd (D : SharpData S κ x ε X K) (u : S.A) (ω : (D.fr u).ι) : ℕ :=
  (D.T u ω * S.d * D.g₀ * D.g₁ * primorial ⌊S.cutX x ε⌋₊) ^ (Module.finrank ℚ K * D.R.N D.R.m * D.wB u)

/-- **A cap for the negative part `𝔞⁻` of `𝔞_ω = 𝔞⁺(𝔞⁻)⁻¹`** (L6.5, verify C8): the archive's `𝔞_ω` is fractional,
with `sg(ω, w) < 0` where its error term `E` dominates: over `T_ω` (`E = EatT`) and over the primes `p > X″` of `DGam`
(`E ≥ v_p(DGam)`), a common multiple of the stabiliser orders (spec L2.3) not defined here. The cap is
`(T_ω·d·g₀g₁·∏_{p ≤ max(X″, N_m[E:ℚ] + 1)} p)^{[K:ℚ]·N_m·wB(u)}`, generous on both counts. Its support adds to `T_ω`
the support of `aBd` (where `sg` may be negative too) and every prime up to `N_m[E:ℚ] + 1`, which holds the primes of
the stabiliser orders: a stabiliser element is fixed by its unitary part, an automorphism of a lattice of `ℤ`-rank at
most `N_m[E:ℚ]`, and a prime dividing the order of a finite subgroup of `GL_n(ℤ)` is at most `n + 1` (Minkowski). A
`DGam` with other primes above `X″` would need them added. The exponent, `aBd`'s, is a parameter bound, not derived
from the archive's `E`. -/
def SharpData.aBdN (D : SharpData S κ x ε X K) (u : S.A) (ω : (D.fr u).ι) : ℕ :=
  (D.T u ω * S.d * D.g₀ * D.g₁ * primorial (max ⌊S.cutX x ε⌋₊ (D.R.N D.R.m * Module.finrank ℚ S.E + 1))) ^
    (Module.finrank ℚ K * D.R.N D.R.m * D.wB u)

open Classical in
/-- **The chain shape and constants** of `u` (L0.5–L0.6, L5.3–L5.4; audit 4, pins 2 and 5), for `IsThetaCol`'s
`Shp`, at every level (audit 7, T1a: the twisted levels twist the characters, not the shape): the length is
`m = R.m`, and for `j ≤ m` the ranks are `n_j = N_j`, the weights `e_j` are those of `hc u` (`eW`), and
`λ_j = WeylFock.wt … j` with `u_i − ½`, `e` of the word's HC family `hw` (as `lamW` at `j = m`; in `RealisedPinned`
`hw = hcW ω`, equal to `hc u` in `v`, `b`, `e`, `u_0`, `u_{k−1}`: the archive's `hcW u`); the coset integers are
`cA = (∏_{P ∈ SG} N P)^{m+1}` and `cB = T_ω·(∏_{P ∈ SG} N P)^{m+1}` at every step (spec-5 §2: the canonical
constants `A = B = m + 1`), over the row set `SG ∪ Q` (spec-7 §3f: `cA = (∏_{P ∈ SG ∪ Q} N P)^{m+1}`, `cB = T_ω·cA`);
`sd = √d/2`. -/
def SharpData.Shp (D : SharpData S κ x ε X K) {τK : Φ S.A → (S.E →+* K)} (u : S.A)
    (ω : (D.fr u).ι) (hw : D.R.HCFamily) (D' : Data τK) (m' : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 S.E))) :
    Prop :=
  (∀ j, D'.cA j = (∏ P ∈ D'.SG ∪ Q, Ideal.absNorm P.asIdeal) ^ (m' + 1) ∧
      D'.cB j = D.T u ω * (∏ P ∈ D'.SG ∪ Q, Ideal.absNorm P.asIdeal) ^ (m' + 1)) ∧
  (m' = D.R.m ∧ (∀ j ≤ m', D'.n j = D.R.N j) ∧ (∀ j ≤ m', D'.e j = D.eW u j) ∧
    ∀ j ≤ m', ∀ (h : D'.n j = D.R.k + j * (D.R.t + 1)) ρ i, D'.lam j ρ i =
      WeylFock.wt D.R.k D.R.t j (fun ρ i => ⌊(hw ρ).u i - 1 / 2⌋) (fun ρ => finN (hw ρ).e) ρ
        (Fin.cast h i)) ∧
    D'.P.sd = Real.sqrt S.d / 2

open Classical in
/-- **Realised, pinned**: `SharpData.Realised thetaHook` over a field `K` normal over `ℚ` with a star (the archive's
`Fields.Ok`: `IsThetaCol` makes the star complex conjugation at the chain's `σ₀`; `K` need not be CM), with the
chain's CM type equal to `τ_K`,
the branching maps pinned (`BrPinned`) at `λ_ω = λ_m` (`lamW`) of the word's HC family `hcW ω` (the archive's `hcW u`:
equal to `hc u` in `v`, `b`, `e`, `u_0`, `u_{k−1}`, so the words may differ in the middle `u_i`; the chain weights `λ_j`
of `Shp`, `λ_0` included, are `hcW ω`'s) and `σ = sgT` (`sgW`) of `hc u`, the source lattices `M_ω`
the `O_K`-span of the integral forms `HermForms.Mω` of `X ⊓ V_ω` and the source metric at each place `v` the complex
Petersson form `H_{ω,σ_v}` (`HermForms.petAt`; both through the word's isomorphism `e ω` with `X_ω ⊓ V_ω`, the one
`IsThetaCol` reads at every level; metrics by `KFrame.RealisesPet`), nonzero row spaces at the twisted levels, the
untwisted level the decorated lattices with `ST = ∅` on the chains' `SG` (`lsh = N`, the chains' points, spec-8 F4),
per word `tz_ω` the element `(a + b√−d)/2` of
`T_ω` (up to conjugation; each word its own `T_ω`, as the archive's `Pr.T u`, `Pr.piT u`), `𝔞⁺ ∣ aBd` and
`𝔞⁻ ∣ aBdN`, and one pin (`pin`) for the base thetas of every step of every chain (audit 13; the archive's
`Base`). The chain shape and `sd` at every level are `SharpData.Shp`. `SG` is half the places over `g₀g₁` (spec-5
§2: all places over `conj(π_{g₀})`, `conj(π_{g₁})`, `f` per prime): every place over `g₀g₁` is in `SG` or in
`conj SG`, and not both (`SG ∩ conj SG = ∅`); `ST_ω` is the set of places over `π_{T_ω} = conj(tz_ω)` (L2.3). The row
spaces are pinned at every level by one clause (spec-9; module docstring, "Rows"): on the decorated lattices with `ST =
∅` and `SG ∪ QE μ` (`QE μ` the row places `IsThetaCol` reads at `μ`), level `rowLevel SG (QE μ)` (through `eX μ`, the
points `IsThetaCol` reads, its top step mapping to the decorated lift `tilQ tz_ω`, `tz_ω ∈ O_E` the integer `P.tz ω`),
`lsh = N`, finitely many classes, and `V0_μ` read
off `V0pt = idemOf X (Amb ⊓ AmbPt)` at representatives, with one `X` (nonempty, irreducible) for all levels, the type
group `∏_{w ∈ SG} GL_r(O_E/w)`, `r = k + m − 1` (`rr`), through `levi`, the level `Psym` with `j ∘ ψ = chiSym xi0`, and
`rowChar` from the residues (`Hecke.ResAt`) of the lift characters `mu0` (the ones every `IsThetaCol` reads) at `SG` and
of `ξT μ` at `QE μ`. One `xi0` (spec-2 item 2) serves every `IsThetaCol` and the row space: `xi0 = −1/(N·√−d)` with `N >
0` (the archive's `N(cc)`, not tied to the pin's `cc`), a unit at every `w ∈ SG`. The level's twist is `ξT μ`: `δ_ℓ·ψ_w`
at `μ(w)`, and of `GoodTw` only a finiteness: for every word, the `w`-integral sources at `μ(w)` and at `μ0`, both in
`V_ω`, have a finite index at `w` (module docstring, "Twist characters"); `pde ≠ pde′`. The archive's index bound
`Σ_{j,b} ε_{j,b} ≤ ℓ⁻²` is on the step-`j` theta image lattices, per lift step `j` and side `b`, which the frontier
does not reach; dropping it keeps the frontier true, and it stays sharp (no free non-unit scalar on the twisted
columns: the shared `e` and pin, `ze` a unit, `Shp`, `TwNF`, `XiFull` at every level; the dropped clause was
one-sided; `ψ_w` an arithmetic choice). Unchecked: whether a choice of `Q_w` (`N P ≡ 1 mod ℓ^K`) puts an `ℓ`-adic
non-unit into the twisted `volN` at `Q`. -/
def SharpData.RealisedPinned (D : SharpData S κ x ε X K) : Prop :=
  ∃ (_ : Normal ℚ K) (_ : StarRing K) (τK : Φ S.A → (S.E →+* K)) (j : K →+* ℂ), (∀ ρ, j.comp (τK ρ) = S.τ ρ) ∧
    ∀ u ∈ A₀ κ, ∃ (T : Type) (G X : T → Type) (_ : ∀ μ, Group (G μ)) (_ : ∀ μ, MulAction (G μ) (X μ))
      (Vs : (D.fr u).ι → Type) (_ : ∀ ω, AddCommGroup (Vs ω)) (_ : ∀ ω, Module K (Vs ω))
      (_ : ∀ ω, Module (𝓞 K) (Vs ω)) (_ : ∀ ω, IsScalarTower (𝓞 K) K (Vs ω))
      (ST : (D.fr u).ι → Finset (HeightOneSpectrum (𝓞 S.E))) (SG : Finset (HeightOneSpectrum (𝓞 S.E)))
      (P : PeriodTarget.PerData (Φ S.A) (D.R.N D.R.m - 1) S.E K G X Vs)
      (μ0 : T) (tw : PeriodTarget.Twist P μ0) (𝔞p 𝔞n : (D.fr u).ι → Ideal (𝓞 K))
      (M : ∀ ω, Submodule (𝓞 K) (Vs ω))
      (hcW : (D.fr u).ι → D.R.HCFamily) (n0 : ℕ) (lam0 : (D.fr u).ι → Φ S.A → Fin n0 → ℤ)
      (χ0 : (D.fr u).ι → (uniUT SG n0 →* K))
      (Xc : ∀ ω, Submodule K (HermForms.Fn (ST ω) (uniUT SG n0) (Φ S.A) K))
      (e : ∀ ω, Vs ω ≃ₗ[K] ↥(Xc ω ⊓ HermForms.Vω (ST ω) τK (χ0 ω) (lam0 ω)))
      (QE : T → Finset (HeightOneSpectrum (𝓞 S.E))) (xi0 : S.E) (ξT : T → Hecke S.E K) (mu0 : ℕ → Hecke S.E K)
      (s : ℝ) (pin : ThetaNorm.Pin (Φ S.A) s)
      (tzO : (D.fr u).ι → 𝓞 S.E) (eX : ∀ μ, X μ ≃ points (E := S.E) (ST := (∅ : Finset (HeightOneSpectrum (𝓞 S.E))))
        (RowSpace.rowLevel (D.R.N D.R.m - 1) D.rr D.R.t SG (QE μ))),
      (∀ μ ω, IsThetaCol τK (D.eW u) D.Sg (D.R.N D.R.m - 1) (μ = μ0) (QE μ) xi0 mu0 pin
        (fun D' k Q ξ => D.Shp u ω (hcW ω) D' k Q ∧ ∀ x, ξ.toHom x = (ξT μ).toHom x) (tzO ω)
        (fun x => (eX μ x).1) (e ω) (P.col μ ω)) ∧
        ((∃ (Ncc : ℕ) (s : S.E), 0 < Ncc ∧ s ^ 2 = -(S.d : S.E) ∧ xi0 * ((Ncc : S.E) * s) = -1) ∧
          ∀ w ∈ SG, w.valuation S.E xi0 = 1) ∧
        BrPinned τK P (fun ω => D.lamW (hcW ω)) (D.sgW u) ∧
        (∀ ω ρ, (hcW ω ρ).v = (D.hc u ρ).v ∧ (hcW ω ρ).b = (D.hc u ρ).b ∧ (hcW ω ρ).e = (D.hc u ρ).e ∧
          ∀ i : Fin D.R.k, ((i : ℕ) = 0 ∨ (i : ℕ) = D.R.k - 1) → (hcW ω ρ).u i = (D.hc u ρ).u i) ∧
        (∀ ω, M ω = Submodule.span (𝓞 K) {φ | (e ω φ).1 ∈ HermForms.Mω (ST ω) τK (χ0 ω) (lam0 ω)}) ∧
        (∃ (pde pde' : ℕ) (δ δ' : Hecke S.E K) (ψ : HeightOneSpectrum (𝓞 K) → Hecke S.E K)
            (Qψ : HeightOneSpectrum (𝓞 K) → Set (HeightOneSpectrum (𝓞 S.E))),
          pde.Prime ∧ pde'.Prime ∧ pde ≠ pde' ∧ δ.IsDelta pde ∧ δ'.IsDelta pde' ∧
          (∀ ω, D.T u ω ≠ pde ∧ D.T u ω ≠ pde') ∧
          ∀ w ∈ tw.Tw, let ℓ := ringChar (𝓞 K ⧸ w.asIdeal)
            let δℓ := if ℓ = pde then δ' else δ
            tw.μw w ≠ μ0 ∧ (ψ w).IsPsi ℓ (Qψ w) ∧ (∀ x, (ξT (tw.μw w)).toHom x = δℓ.toHom x * (ψ w).toHom x) ∧
            ∀ ω, let A := {φ : Vs ω | ∀ r ∈ P.R τK (tw.μw w), P.P (tw.μw w) ω φ r ∈ Ow w}
              let B := {φ : Vs ω | ∀ r ∈ P.R τK μ0, P.P μ0 ω φ r ∈ Ow w}
              (Submodule.span (Ow w) B).toAddSubgroup.relIndex (Submodule.span (Ow w) (A ∪ B)).toAddSubgroup ≠ 0) ∧
        (∀ w ∈ tw.Tw, P.V0 (tw.μw w) ≠ ⊥) ∧
        (∃ (cS : ℕ → ∀ w : HeightOneSpectrum (𝓞 S.E), MulChar (𝓞 S.E ⧸ w.asIdeal) K)
            (cQ : T → ∀ w : HeightOneSpectrum (𝓞 S.E), MulChar (𝓞 S.E ⧸ w.asIdeal) K)
            (_ : Fintype (∀ w : SG, GL (Fin D.rr) (𝓞 S.E ⧸ w.1.asIdeal)))
            (_ : Fintype (RowSpace.Psym D.rr D.R.k (D.R.m / 2 - 1) SG))
            (ψ : RowSpace.Psym D.rr D.R.k (D.R.m / 2 - 1) SG →* K)
            (Xg : Finset ((∀ w : SG, GL (Fin D.rr) (𝓞 S.E ⧸ w.1.asIdeal)) → K)),
          (∀ s < D.R.m, ∀ w ∈ SG, (mu0 s).ResAt w (cS s w)) ∧ (∀ μ, ∀ w ∈ QE μ, (ξT μ).ResAt w (cQ μ w)) ∧
          (∀ g, j (ψ g) = RowSpace.chiSym xi0 D.rr D.R.k (g : ∀ w : SG, GL (Fin D.rr) (𝓞 S.E ⧸ w.1.asIdeal))) ∧
          Xg.Nonempty ∧ (∀ χ ∈ Xg, RowSpace.IsIrrChar χ) ∧
          ∀ μ, ∃ (eG : G μ ≃* Grp S.E (D.R.N D.R.m - 1) (SG ∪ QE μ)
                (RowSpace.rowLevel (D.R.N D.R.m - 1) D.rr D.R.t SG (QE μ))),
            (∀ (g : G μ) (x : X μ), (eX μ (g • x)).1 = eG g • (eX μ x).1) ∧ Finite (Cl (G μ) (X μ)) ∧
            (∀ x, P.lsh μ x = (eX μ x).1.N) ∧
            ∀ F, F ∈ P.V0 μ ↔ ∃ φ ∈ RowSpace.V0pt τK P.σ ∅ (RowSpace.rowLevel _ D.rr D.R.t SG (QE μ))
              (fun h => RowSpace.rowChar D.rr D.R.t D.R.m cS (cQ μ) h.1) (RowSpace.levi D.rr D.rr_le SG (QE μ))
              (RowSpace.Psym D.rr D.R.k (D.R.m / 2 - 1) SG) ψ Xg, ∀ c, F c = φ (eX μ c.out)) ∧
        (∀ v : HeightOneSpectrum (𝓞 S.E), ((D.g₀ * D.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal → v ∈ SG ∨
          ∃ w ∈ SG, v.asIdeal = w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E)) ∧
        (∀ v ∈ SG, ((D.g₀ * D.g₁ : ℕ) : 𝓞 S.E) ∈ v.asIdeal) ∧
        (∀ v ∈ SG, ∀ w ∈ SG,
          v.asIdeal ≠ w.asIdeal.comap (IsCMField.ringOfIntegersComplexConj S.E : 𝓞 S.E →+* 𝓞 S.E)) ∧
        (∀ ω v, v ∈ ST ω ↔ v.valuation S.E (IsCMField.complexConj S.E (P.tz ω)) < 1) ∧
        (∀ ω, (tzO ω : S.E) = P.tz ω) ∧
        (∀ ω, ∃ (a b : ℤ) (s : S.E), s ^ 2 = -(S.d : S.E) ∧ 4 * (D.T u ω : ℤ) = a ^ 2 + S.d * b ^ 2 ∧
          ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ) ∣ b ∧
          a ≡ b + 2 [ZMOD 2 * ((S.QS * S.q * S.d * (D.g₀ * D.g₁) ^ 2 : ℕ) : ℤ)] ∧
          P.tz ω = ((a : S.E) + (b : S.E) * s) / 2) ∧
        (∀ ω, ((D.aBd u ω : ℕ) : 𝓞 K) ∈ 𝔞p ω ∧ ((D.aBdN u ω : ℕ) : 𝓞 K) ∈ 𝔞n ω) ∧
        (D.fr u).RealisesPet τK P μ0 tw 𝔞p 𝔞n M
          fun ω σ φ ψ => HermForms.petAt (ST ω) (lam0 ω) σ (e ω φ).1 (e ω ψ).1

/-- Pinned realisation gives realisation with the theta hook. -/
theorem SharpData.RealisedPinned.realised {D : SharpData S κ x ε X K} (h : D.RealisedPinned) :
    D.Realised thetaHook := by
  obtain ⟨_, _, τK, j, hj, hu⟩ := h
  refine ⟨τK, j, hj, fun u hu' => ?_⟩
  obtain ⟨T, G, X, i1, i2, Vs, i3, i4, i5, i6, ST, SG, P, μ0, tw, 𝔞p, 𝔞n, M, _, n0, lam0, χ0, Xc, e, QE, xi0, _, _,
    s, pin, tzO, eX, hc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hR⟩ := hu u hu'
  exact ⟨T, G, X, i1, i2, Vs, i3, i4, i5, i6, P, μ0, tw, 𝔞p, 𝔞n, M,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, τK, _, _, SG, s, pin,
      fun ω => ⟨ST ω, tzO ω, n0, lam0 ω, χ0 ω, Xc ω, e ω, fun μ => ⟨_, _, _, _, _, _, hc μ ω⟩⟩⟩,
    hR.realises τK⟩

/-- **The pinned sharp frontier**: `SharpBoundTheta`'s shape, with pinned realisation (`τ_K` in the chain, `br`
pinned) and the arithmetic of the parameters (`SharpData.Arith`). -/
def SharpBoundPinned : Prop :=
  ∀ (f : ℕ) [NeZero f] (χ : DirichletCharacter ℂ f), χ.IsPrimitive → ∀ ε₀ > 0, ∃ ε, 0 < ε ∧ ε < ε₀ ∧
    ∃ A ≥ (1 : ℝ), ∀ᶠ Y in Filter.atTop, ∀ q d, ZetaTwist.WinPair ε Y q d →
      ∃ Y' ∈ Set.Icc Y (Y ^ (A / 2)), ∀ x ∈ Set.Icc Y' (Y' ^ 2), ∃ (S : Setting) (κ : S.A →* ℂˣ), S.q = q ∧
        S.d = d ∧ S.d % 4 = 3 ∧ S.Lifts κ χ ∧ ∃ (K : Type) (_ : Field K) (_ : NumberField K)
          (_ : IsTotallyComplex K) (D : SharpData S κ x ε (((S.N : ℝ) * x) ^ Real.log x) K),
            D.RealisedPinned ∧ D.Arith

/-- The pinned frontier implies `SharpBoundTheta`. -/
theorem sharpBoundTheta_of_pinned (h : SharpBoundPinned) : SharpBoundTheta := by
  intro f _ χ hχ ε₀ hε₀
  obtain ⟨ε, hε, hεε₀, A, hA, hY⟩ := h f χ hχ ε₀ hε₀
  refine ⟨ε, hε, hεε₀, A, hA, hY.mono fun Y hY q d hp => ?_⟩
  obtain ⟨Y', hY', hx⟩ := hY q d hp
  refine ⟨Y', hY', fun x hx' => ?_⟩
  obtain ⟨S, κ, hq, hd, hd4, hL, K, _, _, _, D, hD, -⟩ := hx x hx'
  exact ⟨S, κ, hq, hd, hd4, hL, K, _, _, _, D, hD.realised⟩

/-- **CONDITIONAL. RH and GRH from the pinned frontier** (on the half-plane `Re s > 11/12`). -/
theorem rhAndGRH_of_sharpBoundPinned (h : SharpBoundPinned) : HalfPlaneGRH.RHandGRH :=
  rhAndGRH_of_sharpBoundTheta (sharpBoundTheta_of_pinned h)

end

end ZetaBalance
