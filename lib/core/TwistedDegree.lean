import LetterFock

/-!
# Frobenius-twisted column states (T9f)

The mathematical core of C11 (the column systems of the local theorem L5): the column states `K_c` of a path of
dominant weights, their Frobenius-twisted versions `twCol_c`, and the order of their lifts under the lift substitution
`ℓ_g` of `LetterFock`, at plane dimension `r = 1`.

**Conventions** (those of `LetterFock`). Letters are indexed by `ℕ` (the letters `0, …, N − 1` are used), each with
`k` coordinates, coordinate `0` the plane; `vec t` says whether the letter `t` is a vector letter and `pos t ∈ ℕ` is its
orbit position. Positions are nondecreasing on `[0, N]` and stay integers (`ℓ_g` reads `σ^{pos t}`, no reduction mod
`n′`); the final position `z` is `pos N`. A *path* is `μ : ℕ → Fin k → ℤ`, `μ t` the weight after `t` letters; the
height of the column `c ∈ ℤ` in a weight is `colH μ c = #{a : c ≤ μ_a}`. A *state* is a function
`Finset (Fin k) → R` (the coordinates of an element of the exterior algebra), with wedge and contraction
`(y ∧ S)(J) = Σ_{a ∈ J} sg(a, J)·y_a·S(J ∖ a)`, `(y ⌟ S)(J) = Σ_{a ∉ J} sg(a, J)·y_a·S(J ∪ a)`,
`sg(a, J) = (−1)^{#{j ∈ J : a < j}}` (`wedge`, `contr`, `sg`).

**The column states** (`colSt`, generic in the letters, the steps and the powers, for `PathBasis` to reuse). Start at
`[J = ∅]`; at the letter `t`, if the height of column `c` grows, wedge with the letter vector (`c ≥ 1`) or contract with
it (`c ≤ 0`); if it drops, contract (`c ≥ 1`) or wedge (`c ≤ 0`) (`colStep`); then raise every coordinate to the power
`e t`. With `e = 1` and the variable vectors `X_{t,·}` as letters this is `K_c(J)` (`colK`). The twisted state
`twCol_c(J)` (`twCol`) takes `e t = p^{pos(t+1) − pos t}` (`frobExp`). The power is applied after every letter rather
than only before the height-changing ones; this is the same state, as keeping commutes with powers and powers compose;
the powers before the first height change fix `[∅]`, and the last one raises to `p^{z − pos t}`, `t` the last letter.

**Costs and hypotheses.** A letter is *costly* (`costly`) if the height grows at it from `≥ 1` or drops at it from
`≤ 1`; `cost(c) = Σ_{t < N costly} p^{z − pos t}` (`cost … N`; `cost … t` is the cost at stage `t`). `ColCond`: the
height changes by at most one per letter, grows only at vector letters and drops only at covector letters, starts at
`0` for `c ≥ 1`, and for `c ≤ 0` grows only from `≥ 1` and drops only from `≥ 2` (implied by the height staying `> 1`).
`Strict`: if `i < t`, the letter `i` changes the height and `t` is costly, then `pos i < pos t`. A *plane-dominant
joined path* (`JoinCond`) is `μ t = (ν t, κ t)` (`joinPath`): `ν` and `κ` start at `0`; `ν` is nondecreasing and
constant across covector letters; vector letters raise `κ` and covector letters lower it, pointwise; the tangent rows
after a vector letter sit below the plane row before it (`κ_{t+1} ≤ ν_t`, condition (C)); the tangent height of the
column `c` changes by at most one per letter. It implies `ColCond` (`JoinCond.colCond`).

**Main results.**
* (int, `twCol_int`) `twCol_c(J)` over `Kf` is the image of the state over `ℤ`, so it is `O`-integral; (deg,
  `twCol_deg`) it is homogeneous of degree `p^{z − pos t}` in each height-changing letter `t` and `0` in the others.
* (ord, `twCol_ord`) Under `ColCond`, for every `g` over `W` with `det g` a unit, `ℓ_g(twCol_c J)` has order
  `≥ cost(c)`. Strictness is not needed.
* (cong, `twCol_cong`) For a plane-dominant joined path with strictness, at `g = 1`,
  `ℓ_1(twCol_c J) ≡ ϖ^{cost(c)}·Frob_z(planeTan_c(J)) (mod ϖ^{cost(c) + 1})`: `planeTan_c(J)` (`planeTan`) is the
  untwisted column state of the plane path at `J ∩ {0}` times that of the tangent path at `J ∖ {0}`, and
  `Frob_z : X_{t,b} ↦ X_{t,b}^{p^{z − pos t}}` (`frobZ`). The plane state is `X_{t₀,0}` at `{0}` for the letter `t₀`
  adding the plane box of the column `c` (`colK_plane`), and `[∅]` if there is none (`colK_plane_const`).

**The route.** Both are proved over a commutative ring `A` with an element `π` (`ord_core`, `cong_core`) and carried
to `Kf` through `A = O[X]`, `π = C ϖ`: the lifted letters `ℓ_g(X_{t,a})` are images of `O`-polynomials (`lift_data`).
For (ord) the lifted vector letters are `x·v + π·u` and the lifted covector letters `η` have `π ∣ ⟨η, v⟩`, `v` the row
`0` of `σ^{pos t}(g⁻¹)` (the *line*). The order invariant of a state `T` does not see the frame of `g`: `π^C ∣ T` and,
in positive degree, `π^{C+1} ∣ v ∧ T` for `c ≥ 1` (`InvW`), resp. `π^{C+1} ∣ v ⌟ T` for `c ≤ 0` (`InvC`). Wedging
`x·v + π·u` raises `C` by one exactly in positive degree (`v ∧ v = 0`, anticommutation); contracting `η` keeps it, by
the derivation rule `η ⌟ (v ∧ T) + v ∧ (η ⌟ T) = ⟨η, v⟩·T` (`contr_wedge`), except the drop to degree `0`, which costs
one, through a unimodular `φ` (`⟨φ, v⟩ = 1`, the column `0` of `σ^{pos t}(g)`); dually for `c ≤ 0`. The Frobenius
power multiplies `C` by `p^d` and moves the line to `v(pos t + d) ≡ v(pos t)^{p^d} (mod p)` (`frob_pow`), since
`(Σ ±y_i·S_i)^{p^d} ≡ Σ ±y_i^{p^d}·S_i^{p^d}` modulo `p·π^{p^d·C}` when `π^C ∣ S_i` (`frob_signed`). No
functoriality of exterior powers is needed. For (cong) the letters at `g = 1` are scaled diagonally (`ysc`), and the
invariant (`InvL`, `InvD`) records the leading term `π^C·Pl(J ∩ 0)·Tan(J ∖ 0)` of the twisted joined state, the
off-type coordinates (`0 ∉ J` for `c ≥ 1`, `0 ∈ J` for `c ≤ 0`) having order `≥ C + 1`, and `≥ C + 2` when *fresh*
(`fresh`: a Frobenius power `≥ p` since the last height change). Strictness makes every costly letter fresh, which
removes the off-type sub-states from the leading term of a costly step. The twisted plane and tangent states are the
Frobenius twists of the untwisted ones modulo `p` (`tw_frob`), and `π ∣ p`.

**Readings of the planning statement.** The spec's `Dvd ϖ i F` is `OrdGe ϖ i F` and `lift_g` is
`liftSub ι σ ϖ 1 vec pos g`. Only plane dimension `r = 1` is done. The tangent strip condition of `JoinCond` is stated
on column heights; the Pieri-path form is `PathBasis`'s.
-/

namespace TwistedDegree

open MvPolynomial Finset LetterFock InertModel

noncomputable section

/-! ## Wedge and contraction on coordinate states -/

section Exterior

variable {R : Type*} [CommRing R] {k : ℕ}

/-- **The sign** `(−1)^{#{j ∈ J : a < j}}` of the coordinate `a` in `J`. -/
def sg (a : Fin k) (J : Finset (Fin k)) : R := (-1) ^ (J.filter (a < ·)).card

/-- **Wedge with a vector**: `(y ∧ S)(J) = Σ_{a ∈ J} sg(a, J)·y_a·S(J ∖ a)`. -/
def wedge (y : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) : R :=
  ∑ a ∈ J, sg a J * y a * S (J.erase a)

/-- **Contraction with a vector**: `(y ⌟ S)(J) = Σ_{a ∉ J} sg(a, J)·y_a·S(J ∪ a)`. -/
def contr (y : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) : R :=
  ∑ a ∈ Jᶜ, sg a J * y a * S (insert a J)

/-- **The sign squares to one.** -/
theorem sg_mul_self (a : Fin k) (J : Finset (Fin k)) : (sg a J : R) * sg a J = 1 := by
  rw [sg, ← pow_add, ← two_mul, pow_mul]
  simp

/-- **The sign after removing another coordinate** `b`: it flips iff `a < b`. -/
theorem sg_erase {a b : Fin k} {J : Finset (Fin k)} (hb : b ∈ J) :
    (sg a (J.erase b) : R) = (if a < b then -1 else 1) * sg a J := by
  unfold sg
  rw [Finset.filter_erase]
  split_ifs with h
  · have hm : b ∈ J.filter (a < ·) := Finset.mem_filter.2 ⟨hb, h⟩
    rw [Finset.card_erase_of_mem hm]
    have hpos : 0 < (J.filter (a < ·)).card := Finset.card_pos.2 ⟨b, hm⟩
    conv_rhs => rw [← Nat.sub_add_cancel hpos, pow_succ]
    ring
  · rw [Finset.erase_eq_of_notMem (by simp [h]), one_mul]

/-- **The sign after adding another coordinate** `b`: it flips iff `a < b`. -/
theorem sg_insert {a b : Fin k} {J : Finset (Fin k)} (hb : b ∉ J) :
    (sg a (insert b J) : R) = (if a < b then -1 else 1) * sg a J := by
  unfold sg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hb]), pow_succ]
    ring
  · rw [one_mul]

/-- **The sign of `a` does not see `a` itself.** -/
theorem sg_erase_self (a : Fin k) (J : Finset (Fin k)) : (sg a (J.erase a) : R) = sg a J := by
  unfold sg
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp)]

/-- **The sign of `a` does not see `a` itself**, inserting. -/
theorem sg_insert_self (a : Fin k) (J : Finset (Fin k)) : (sg a (insert a J) : R) = sg a J := by
  unfold sg
  rw [Finset.filter_insert, ite_eq_right_iff.2 fun h => absurd h (lt_irrefl a)]

/-- **Swapping two distinct coordinates flips the product of the sign changes.** -/
theorem sg_swap {a b : Fin k} (hab : a ≠ b) :
    ((if b < a then -1 else 1) + (if a < b then -1 else 1) : R) = 0 := by
  rcases lt_or_gt_of_ne hab with h | h
  · simp [h, not_lt.2 h.le]
  · simp [h, not_lt.2 h.le]

/-- **A double sum over distinct pairs of an antisymmetric function vanishes.** -/
theorem sum_offDiag_anti (s : Finset (Fin k)) (F : Fin k → Fin k → R)
    (hF : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → F a b + F b a = 0) :
    ∑ a ∈ s, ∑ b ∈ s.erase a, F a b = 0 := by
  rw [← Finset.sum_finset_product' s.offDiag s (fun a => s.erase a) (fun x => by
    simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)]
  refine Finset.sum_involution (fun x _ => x.swap) (fun x hx => ?_) (fun x hx _ => ?_) (fun x hx => ?_)
    (fun x _ => Prod.swap_swap x)
  · exact hF _ (Finset.mem_offDiag.1 hx).1 _ (Finset.mem_offDiag.1 hx).2.1 (Finset.mem_offDiag.1 hx).2.2
  · exact fun h => (Finset.mem_offDiag.1 hx).2.2 ((Prod.ext_iff.1 h).1).symm
  · simp only [Finset.mem_offDiag, Prod.fst_swap, Prod.snd_swap] at hx ⊢
    exact ⟨hx.2.1, hx.1, Ne.symm hx.2.2⟩

/-- **`y ∧ y ∧ S = 0`.** -/
theorem wedge_wedge_self (y : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    wedge y (wedge y S) J = 0 := by
  unfold wedge
  simp_rw [Finset.mul_sum]
  refine sum_offDiag_anti J _ fun a ha b hb hab => ?_
  rw [sg_erase ha, sg_erase hb, Finset.erase_right_comm]
  have := sg_swap (R := R) hab
  linear_combination (sg a J * sg b J * y a * y b * S ((J.erase b).erase a)) * this

/-- **`y ⌟ y ⌟ S = 0`.** -/
theorem contr_contr_self (y : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    contr y (contr y S) J = 0 := by
  unfold contr
  simp_rw [Finset.mul_sum, Finset.compl_insert]
  refine sum_offDiag_anti Jᶜ _ fun a ha b hb hab => ?_
  rw [sg_insert (Finset.mem_compl.1 ha), sg_insert (Finset.mem_compl.1 hb), Finset.insert_comm]
  have := sg_swap (R := R) hab
  linear_combination (sg a J * sg b J * y a * y b * S (insert a (insert b J))) * this

/-- **Contraction is a derivation of the wedge**: `φ ⌟ (y ∧ S) + y ∧ (φ ⌟ S) = ⟨φ, y⟩·S`. -/
theorem contr_wedge (φ y : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    contr φ (wedge y S) J + wedge y (contr φ S) J = (∑ a, φ a * y a) * S J := by
  unfold contr wedge
  have h1 : ∀ a ∈ Jᶜ, sg a J * φ a * ∑ b ∈ insert a J, sg b (insert a J) * y b * S ((insert a J).erase b) =
      φ a * y a * S J + ∑ b ∈ J, sg a J * φ a * (sg b (insert a J) * y b * S (insert a (J.erase b))) := by
    intro a ha
    have ha' : a ∉ J := Finset.mem_compl.1 ha
    rw [Finset.sum_insert ha', mul_add, Finset.mul_sum, sg_insert_self, Finset.erase_insert ha']
    congr 1
    · linear_combination (φ a * y a * S J) * sg_mul_self (R := R) a J
    · exact Finset.sum_congr rfl fun b hb => by rw [Finset.erase_insert_of_ne (by rintro rfl; exact ha' hb)]
  have h2 : ∀ b ∈ J, sg b J * y b * ∑ a ∈ (J.erase b)ᶜ, sg a (J.erase b) * φ a * S (insert a (J.erase b)) =
      φ b * y b * S J + ∑ a ∈ Jᶜ, sg b J * y b * (sg a (J.erase b) * φ a * S (insert a (J.erase b))) := by
    intro b hb
    rw [Finset.compl_erase, Finset.sum_insert (by simp [hb]), mul_add, Finset.mul_sum, sg_erase_self,
      Finset.insert_erase hb]
    congr 1
    linear_combination (φ b * y b * S J) * sg_mul_self (R := R) b J
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_comm (s := J) (t := Jᶜ)]
  have hoff : ∑ a ∈ Jᶜ, ∑ b ∈ J, (sg a J * φ a * (sg b (insert a J) * y b * S (insert a (J.erase b))) +
      sg b J * y b * (sg a (J.erase b) * φ a * S (insert a (J.erase b)))) = 0 := by
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    have ha' : a ∉ J := Finset.mem_compl.1 ha
    have hab : a ≠ b := fun h => ha' (h ▸ hb)
    rw [sg_insert ha', sg_erase hb]
    have := sg_swap (R := R) hab
    linear_combination (sg a J * sg b J * φ a * y b * S (insert a (J.erase b))) * this
  have hoff' : ∑ a ∈ Jᶜ, ∑ b ∈ J, sg a J * φ a * (sg b (insert a J) * y b * S (insert a (J.erase b))) +
      ∑ a ∈ Jᶜ, ∑ b ∈ J, sg b J * y b * (sg a (J.erase b) * φ a * S (insert a (J.erase b))) = 0 := by
    rw [← hoff, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib.symm
  have e : ∑ a ∈ Jᶜ, φ a * y a * S J + ∑ b ∈ J, φ b * y b * S J = (∑ a, φ a * y a) * S J := by
    rw [add_comm, Finset.sum_add_sum_compl, Finset.sum_mul]
  linear_combination e + hoff'

/-- **Wedge is linear in the vector.** -/
theorem wedge_lin (x z : R) (v u : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    wedge (fun a => x * v a + z * u a) S J = x * wedge v S J + z * wedge u S J := by
  simp only [wedge, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Wedge is linear in the state.** -/
theorem wedge_lin_st (y : Fin k → R) (x z : R) (S S' : Finset (Fin k) → R) (J : Finset (Fin k)) :
    wedge y (fun J => x * S J + z * S' J) J = x * wedge y S J + z * wedge y S' J := by
  simp only [wedge, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Contraction is linear in the vector.** -/
theorem contr_lin (x z : R) (v u : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    contr (fun a => x * v a + z * u a) S J = x * contr v S J + z * contr u S J := by
  simp only [contr, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Contraction is linear in the state.** -/
theorem contr_lin_st (y : Fin k → R) (x z : R) (S S' : Finset (Fin k) → R) (J : Finset (Fin k)) :
    contr y (fun J => x * S J + z * S' J) J = x * contr y S J + z * contr y S' J := by
  simp only [contr, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Wedges anticommute.** -/
theorem wedge_anti (v u : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    wedge v (wedge u S) J = -wedge u (wedge v S) J := by
  have h := wedge_wedge_self (fun a => 1 * v a + 1 * u a) S J
  have e : wedge (fun a => 1 * v a + 1 * u a) S = fun J => 1 * wedge v S J + 1 * wedge u S J :=
    funext fun J => wedge_lin 1 1 v u S J
  rw [e, wedge_lin, wedge_lin_st, wedge_lin_st, wedge_wedge_self, wedge_wedge_self] at h
  linear_combination h

/-- **Contractions anticommute.** -/
theorem contr_anti (v u : Fin k → R) (S : Finset (Fin k) → R) (J : Finset (Fin k)) :
    contr v (contr u S) J = -contr u (contr v S) J := by
  have h := contr_contr_self (fun a => 1 * v a + 1 * u a) S J
  have e : contr (fun a => 1 * v a + 1 * u a) S = fun J => 1 * contr v S J + 1 * contr u S J :=
    funext fun J => contr_lin 1 1 v u S J
  rw [e, contr_lin, contr_lin_st, contr_lin_st, contr_contr_self, contr_contr_self] at h
  linear_combination h

/-- **Divisibility passes to the wedge.** -/
theorem dvd_wedge {d : R} {S : Finset (Fin k) → R} (hS : ∀ J, d ∣ S J) (y : Fin k → R) (J : Finset (Fin k)) :
    d ∣ wedge y S J :=
  Finset.dvd_sum fun _ _ => Dvd.dvd.mul_left (hS _) _

/-- **Divisibility passes to the contraction.** -/
theorem dvd_contr {d : R} {S : Finset (Fin k) → R} (hS : ∀ J, d ∣ S J) (y : Fin k → R) (J : Finset (Fin k)) :
    d ∣ contr y S J :=
  Finset.dvd_sum fun _ _ => Dvd.dvd.mul_left (hS _) _

/-- **The wedge raises the degree.** -/
theorem wedge_supp {S : Finset (Fin k) → R} {h : ℕ} (hS : ∀ J, J.card ≠ h → S J = 0) (y : Fin k → R)
    {J : Finset (Fin k)} (hJ : J.card ≠ h + 1) : wedge y S J = 0 :=
  Finset.sum_eq_zero fun a ha => by
    rw [hS _ (by rw [Finset.card_erase_of_mem ha]; have := Finset.card_pos.2 ⟨a, ha⟩; omega), mul_zero]

/-- **The contraction lowers the degree.** -/
theorem contr_supp {S : Finset (Fin k) → R} {h : ℕ} (hS : ∀ J, J.card ≠ h → S J = 0) (y : Fin k → R)
    {J : Finset (Fin k)} (hJ : J.card + 1 ≠ h) : contr y S J = 0 :=
  Finset.sum_eq_zero fun a ha => by
    rw [hS _ (by rw [Finset.card_insert_of_notMem (Finset.mem_compl.1 ha)]; exact hJ), mul_zero]

end Exterior

/-! ## Frobenius congruences -/

section Frobenius

variable {R : Type*} [CommRing R] {k p : ℕ}

/-- **Fermat for integers**: `x^{p^d} ≡ x (mod p)`. -/
theorem int_pow_sub_dvd (hp : p.Prime) (x : ℤ) (d : ℕ) : (p : ℤ) ∣ x ^ p ^ d - x := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card_pow, sub_self]

/-- **The freshman's dream** for a finite sum: `(Σ f)^{p^d} ≡ Σ f^{p^d} (mod p)`. -/
theorem sum_pow_prime_pow (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → R) (d : ℕ) :
    ∃ r, (∑ i ∈ s, f i) ^ p ^ d = ∑ i ∈ s, f i ^ p ^ d + p * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [zero_pow (pow_ne_zero _ hp.ne_zero)]⟩
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (f a) (∑ i ∈ s, f i) d
    exact ⟨f a * (∑ i ∈ s, f i) * r' + r, by rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]; ring⟩

/-- **The Frobenius congruence of a signed sum with a factor of order `C`**: with `π^C ∣ S_i`,
`(Σ ±y_i·S_i)^{p^d} ≡ Σ ±y_i^{p^d}·S_i^{p^d}` modulo `p·π^{p^d·C}`. -/
theorem frob_signed (hp : p.Prime) {ι : Type*} (s : Finset ι) (n : ι → ℕ) (y S : ι → R) {π : R} {C : ℕ}
    (hS : ∀ i, π ^ C ∣ S i) (d : ℕ) :
    (p : R) * π ^ (p ^ d * C) ∣ (∑ i ∈ s, (-1) ^ n i * y i * S i) ^ p ^ d -
      ∑ i ∈ s, (-1) ^ n i * y i ^ p ^ d * S i ^ p ^ d := by
  choose S₀ hS₀ using hS
  obtain ⟨r, hr⟩ := sum_pow_prime_pow hp s (fun i => (-1) ^ n i * y i * S₀ i) d
  choose rr hrr using fun i => int_pow_sub_dvd hp ((-1) ^ n i) d
  have e1 : ∑ i ∈ s, (-1) ^ n i * y i * S i = π ^ C * ∑ i ∈ s, (-1) ^ n i * y i * S₀ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hS₀]; ring
  have e2 : ∑ i ∈ s, (-1) ^ n i * y i ^ p ^ d * S i ^ p ^ d =
      π ^ (p ^ d * C) * ∑ i ∈ s, (-1) ^ n i * y i ^ p ^ d * S₀ i ^ p ^ d := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hS₀, mul_pow, ← pow_mul, mul_comm C]; ring
  have e3 : ∑ i ∈ s, ((-1) ^ n i * y i * S₀ i) ^ p ^ d = ∑ i ∈ s, (-1) ^ n i * y i ^ p ^ d * S₀ i ^ p ^ d +
      p * ∑ i ∈ s, (rr i : R) * y i ^ p ^ d * S₀ i ^ p ^ d := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := congrArg (Int.cast : ℤ → R) (hrr i)
    push_cast at h
    rw [mul_pow, mul_pow]
    linear_combination (y i ^ p ^ d * S₀ i ^ p ^ d) * h
  refine ⟨∑ i ∈ s, (rr i : R) * y i ^ p ^ d * S₀ i ^ p ^ d + r, ?_⟩
  rw [e1, e2, mul_pow, ← pow_mul, mul_comm C, hr, e3]
  ring

/-- **A coordinatewise power** of a state. -/
def pw (q : ℕ) (S : Finset (Fin k) → R) : Finset (Fin k) → R := fun J => S J ^ q

/-- **The Frobenius congruence of the wedge**: `(y ∧ S)^{p^d} ≡ y^{p^d} ∧ S^{p^d}` modulo `p·π^{p^d·C}` when
`π^C ∣ S`. -/
theorem frob_wedge (hp : p.Prime) {π : R} {C : ℕ} {S : Finset (Fin k) → R} (hS : ∀ J, π ^ C ∣ S J)
    (y : Fin k → R) (d : ℕ) (J : Finset (Fin k)) :
    (p : R) * π ^ (p ^ d * C) ∣ wedge y S J ^ p ^ d - wedge (fun a => y a ^ p ^ d) (pw (p ^ d) S) J :=
  frob_signed hp J (fun a => (J.filter (a < ·)).card) y (fun a => S (J.erase a)) (fun _ => hS _) d

/-- **The Frobenius congruence of the contraction.** -/
theorem frob_contr (hp : p.Prime) {π : R} {C : ℕ} {S : Finset (Fin k) → R} (hS : ∀ J, π ^ C ∣ S J)
    (y : Fin k → R) (d : ℕ) (J : Finset (Fin k)) :
    (p : R) * π ^ (p ^ d * C) ∣ contr y S J ^ p ^ d - contr (fun a => y a ^ p ^ d) (pw (p ^ d) S) J :=
  frob_signed hp Jᶜ (fun a => (J.filter (a < ·)).card) y (fun a => S (insert a J)) (fun _ => hS _) d

end Frobenius


/-! ## Column states -/

section ColState

variable {R : Type*} [CommRing R] {k p : ℕ}

/-- **A step of a column state**: keep, wedge with the letter vector, or contract with it. -/
inductive Step
  | keep
  | wed
  | con

/-- **Applying a step** to a state. -/
def Step.app : Step → (Fin k → R) → (Finset (Fin k) → R) → Finset (Fin k) → R
  | .keep, _, S => S
  | .wed, y, S => wedge y S
  | .con, y, S => contr y S

/-- **The initial state** `[J = ∅]`. -/
def st0 : Finset (Fin k) → R := fun J => if J = ∅ then 1 else 0

/-- **The state after `t` letters**, for letter vectors `y`, steps `st` and exponents `e`: apply the step of the
letter, then raise every coordinate to the power `e t`. -/
def colSt (y : ℕ → Fin k → R) (st : ℕ → Step) (e : ℕ → ℕ) : ℕ → Finset (Fin k) → R
  | 0 => st0
  | t + 1 => pw (e t) ((st t).app (y t) (colSt y st e t))

/-- **One more letter**: the step of the letter, then the power. -/
theorem colSt_succ (y : ℕ → Fin k → R) (st : ℕ → Step) (e : ℕ → ℕ) (t : ℕ) :
    colSt y st e (t + 1) = pw (e t) ((st t).app (y t) (colSt y st e t)) := rfl

/-- **Ring homomorphisms commute with the steps.** -/
theorem map_app {R' : Type*} [CommRing R'] (f : R →+* R') (st : Step) (y : Fin k → R) (S : Finset (Fin k) → R)
    (J : Finset (Fin k)) : f (st.app y S J) = st.app (fun a => f (y a)) (fun J => f (S J)) J := by
  cases st <;> simp [Step.app, wedge, contr, sg, map_sum]

/-- **Ring homomorphisms commute with the column states.** -/
theorem map_colSt {R' : Type*} [CommRing R'] (f : R →+* R') (y : ℕ → Fin k → R) (st : ℕ → Step) (e : ℕ → ℕ)
    (t : ℕ) (J : Finset (Fin k)) : f (colSt y st e t J) = colSt (fun t a => f (y t a)) st e t J := by
  induction t generalizing J with
  | zero => simp only [colSt, st0]; split_ifs <;> simp
  | succ t ih =>
    rw [colSt_succ, colSt_succ, pw, pw, map_pow, map_app]
    exact congrArg (· ^ e t) (congrArg (fun S => (st t).app _ S J) (funext ih))

/-- **The state after `t` letters depends only on the first `t` letters.** -/
theorem colSt_congr {y y' : ℕ → Fin k → R} (st : ℕ → Step) (e : ℕ → ℕ) {t : ℕ} (h : ∀ u < t, y u = y' u) :
    colSt y st e t = colSt y' st e t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [colSt_succ, colSt_succ, h t (Nat.lt_succ_self t), ih fun u hu => h u (by omega)]

/-- **Congruent states give congruent steps.** -/
theorem app_sub_dvd {d : R} {S S' : Finset (Fin k) → R} (h : ∀ J, d ∣ S J - S' J) (st : Step) (y : Fin k → R)
    (J : Finset (Fin k)) : d ∣ st.app y S J - st.app y S' J := by
  cases st
  · exact h J
  · simp only [Step.app, wedge, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.dvd_sum fun _ _ => Dvd.dvd.mul_left (h _) _
  · simp only [Step.app, contr, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.dvd_sum fun _ _ => Dvd.dvd.mul_left (h _) _

/-- **Congruent states give congruent powers.** -/
theorem pw_sub_dvd {d : R} {S S' : Finset (Fin k) → R} (h : ∀ J, d ∣ S J - S' J) (q : ℕ) (J : Finset (Fin k)) :
    d ∣ pw q S J - pw q S' J :=
  (h J).trans (sub_dvd_pow_sub_pow _ _ _)

/-- **The Frobenius congruence of a step**: `(step y S)^{p^d} ≡ step y^{p^d} S^{p^d} (mod p)`. -/
theorem app_frob (hp : p.Prime) (st : Step) (y : Fin k → R) (S : Finset (Fin k) → R) (d : ℕ) (J : Finset (Fin k)) :
    (p : R) ∣ pw (p ^ d) (st.app y S) J - st.app (fun a => y a ^ p ^ d) (pw (p ^ d) S) J := by
  have hS : ∀ J, (1 : R) ^ 0 ∣ S J := fun J => by rw [pow_zero]; exact one_dvd _
  cases st
  · simp [Step.app, pw]
  · simpa [Step.app, pw] using frob_wedge hp hS y d J
  · simpa [Step.app, pw] using frob_contr hp hS y d J

/-- **Frobenius and untwisted states**: `K(y)^{p^d} ≡ K(y^{p^d}) (mod p)` for the states with exponents `1`. -/
theorem colSt_frob (hp : p.Prime) (y : ℕ → Fin k → R) (st : ℕ → Step) (d t : ℕ) (J : Finset (Fin k)) :
    (p : R) ∣ pw (p ^ d) (colSt y st (fun _ => 1) t) J - colSt (fun u a => y u a ^ p ^ d) st (fun _ => 1) t J := by
  induction t generalizing J with
  | zero =>
    simp only [colSt, st0, pw]
    split_ifs <;> simp [zero_pow (pow_ne_zero _ hp.ne_zero)]
  | succ t ih =>
    simp only [colSt_succ]
    have e1 : ∀ S : Finset (Fin k) → R, pw 1 S = S := fun S => funext fun J => pow_one _
    rw [e1, e1]
    have h1 := app_frob hp (st t) (y t) (colSt y st (fun _ => 1) t) d J
    have h2 := app_sub_dvd ih (st t) (fun a => y t a ^ p ^ d) J
    rw [← sub_add_sub_cancel]
    exact dvd_add h1 h2

/-- **Monotonicity from successive steps** on `[0, N]`. -/
theorem mono_of_succ {α : Type*} [Preorder α] {f : ℕ → α} {N : ℕ} (hf : ∀ t < N, f t ≤ f (t + 1)) {u t : ℕ}
    (hut : u ≤ t) (htN : t ≤ N) : f u ≤ f t := by
  induction t, hut using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact (ih (by omega)).trans (hf t (by omega))

/-- **The Frobenius exponents** `p^{pos(t + 1) − pos t}` of a twisted state. -/
def frobExp (p : ℕ) (pos : ℕ → ℕ) (t : ℕ) : ℕ := p ^ (pos (t + 1) - pos t)

/-- **Twisted states are Frobenius twists mod `p`**: the twisted state after `t` letters is congruent mod `p` to the
untwisted state of the letters raised to `p^{pos t − pos u}`. -/
theorem tw_frob (hp : p.Prime) (y : ℕ → Fin k → R) (st : ℕ → Step) {pos : ℕ → ℕ} {N : ℕ}
    (hpos : ∀ t < N, pos t ≤ pos (t + 1)) {t : ℕ} (ht : t ≤ N) (J : Finset (Fin k)) :
    (p : R) ∣ colSt y st (frobExp p pos) t J -
      colSt (fun u a => y u a ^ p ^ (pos t - pos u)) st (fun _ => 1) t J := by
  induction t generalizing J with
  | zero => simp only [colSt, sub_self, dvd_zero]
  | succ t ih =>
    have htN : t < N := by omega
    obtain ⟨d, hd⟩ : ∃ d, pos (t + 1) = pos t + d := ⟨_, (Nat.add_sub_cancel' (hpos t htN)).symm⟩
    have hd' : pos (t + 1) - pos t = d := by omega
    have hY : colSt (fun u a => y u a ^ p ^ (pos (t + 1) - pos u)) st (fun _ => 1) t =
        colSt (fun u a => (y u a ^ p ^ (pos t - pos u)) ^ p ^ d) st (fun _ => 1) t := by
      refine colSt_congr st _ fun u hu => funext fun a => ?_
      have := mono_of_succ hpos hu.le (by omega)
      rw [← pow_mul, ← pow_add, hd]
      congr 2
      omega
    have e1 : ∀ S : Finset (Fin k) → R, pw 1 S = S := fun S => funext fun J => pow_one _
    simp only [colSt_succ, e1, frobExp, hd', hY]
    have h1 := pw_sub_dvd (app_sub_dvd (ih (by omega)) (st t) (y t)) (p ^ d) J
    have h2 := app_frob hp (st t) (y t) (colSt (fun u a => y u a ^ p ^ (pos t - pos u)) st (fun _ => 1) t) d J
    have h3 := app_sub_dvd (colSt_frob hp (fun u a => y u a ^ p ^ (pos t - pos u)) st d t) (st t)
      (fun a => y t a ^ p ^ d) J
    have := dvd_add (dvd_add h1 h2) h3
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this

end ColState

/-! ## Paths, column heights and costs -/

section Path

variable {k : ℕ}

/-- **The height of column `c`** in a weight `μ`: `#{a : c ≤ μ_a}`. -/
def colH (μ : Fin k → ℤ) (c : ℤ) : ℕ := (Finset.univ.filter fun a => c ≤ μ a).card

/-- **The step of column `c` at letter `t`** of a path `μ` (`μ t` the weight after `t` letters): if the height grows,
wedge (`c ≥ 1`) or contract (`c ≤ 0`); if it drops, contract (`c ≥ 1`) or wedge (`c ≤ 0`); otherwise keep. -/
def colStep (μ : ℕ → Fin k → ℤ) (c : ℤ) (t : ℕ) : Step :=
  if colH (μ t) c < colH (μ (t + 1)) c then (if 1 ≤ c then .wed else .con)
  else if colH (μ (t + 1)) c < colH (μ t) c then (if 1 ≤ c then .con else .wed) else .keep

/-- **The step where the height grows.** -/
theorem colStep_grow {μ : ℕ → Fin k → ℤ} {c : ℤ} {t : ℕ} (h : colH (μ t) c < colH (μ (t + 1)) c) :
    colStep μ c t = if 1 ≤ c then .wed else .con := by
  rw [colStep, ite_eq_left h]

/-- **The step where the height drops.** -/
theorem colStep_drop {μ : ℕ → Fin k → ℤ} {c : ℤ} {t : ℕ} (h : colH (μ (t + 1)) c < colH (μ t) c) :
    colStep μ c t = if 1 ≤ c then .con else .wed := by
  rw [colStep, ite_eq_right (not_lt.2 h.le), ite_eq_left h]

/-- **The step where the height stays.** -/
theorem colStep_keep {μ : ℕ → Fin k → ℤ} {c : ℤ} {t : ℕ} (h : colH (μ t) c = colH (μ (t + 1)) c) :
    colStep μ c t = .keep := by
  rw [colStep, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **A costly letter** of column `c`: the height grows at `t` from `≥ 1`, or drops at `t` from `≤ 1`. -/
def costly (μ : ℕ → Fin k → ℤ) (c : ℤ) (t : ℕ) : Prop :=
  colH (μ t) c < colH (μ (t + 1)) c ∧ 1 ≤ colH (μ t) c ∨ colH (μ (t + 1)) c < colH (μ t) c ∧ colH (μ t) c ≤ 1

/-- **Costliness is decidable.** -/
instance (μ : ℕ → Fin k → ℤ) (c : ℤ) : DecidablePred (costly μ c) := fun _ => by
  unfold costly
  infer_instance

/-- **The cost of column `c` at stage `t`**: `Σ_{u < t costly} p^{pos t − pos u}` (`cost(c)` is the stage `N`). -/
def cost (p : ℕ) (pos : ℕ → ℕ) (μ : ℕ → Fin k → ℤ) (c : ℤ) (t : ℕ) : ℕ :=
  ∑ u ∈ Finset.range t, if costly μ c u then p ^ (pos t - pos u) else 0

/-- **The cost recursion**: `cost(t + 1) = p^{pos(t + 1) − pos t}·(cost t + [t costly])`. -/
theorem cost_succ {p : ℕ} {pos : ℕ → ℕ} {N : ℕ} (hpos : ∀ t < N, pos t ≤ pos (t + 1)) (μ : ℕ → Fin k → ℤ)
    (c : ℤ) {t : ℕ} (ht : t < N) :
    cost p pos μ c (t + 1) = p ^ (pos (t + 1) - pos t) * (cost p pos μ c t + if costly μ c t then 1 else 0) := by
  rw [cost, Finset.sum_range_succ, cost, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun u hu => ?_
    have h1 := mono_of_succ hpos (Finset.mem_range.1 hu).le ht.le
    have h2 := hpos t ht
    split_ifs
    · rw [← pow_add]
      congr 1
      omega
    · rw [mul_zero]
  · split_ifs <;> simp

/-- **The column conditions** (ColCond): the height changes by at most one per letter, grows only at vector letters
and drops only at covector letters; for `c ≥ 1` it starts at `0`; for `c ≤ 0` it grows only from `≥ 1` and drops only
from `≥ 2` (implied by the height staying `> 1`). -/
structure ColCond (vec : ℕ → Bool) (μ : ℕ → Fin k → ℤ) (c : ℤ) (N : ℕ) : Prop where
  step : ∀ t < N, colH (μ (t + 1)) c ≤ colH (μ t) c + 1 ∧ colH (μ t) c ≤ colH (μ (t + 1)) c + 1
  grow : ∀ t < N, colH (μ t) c < colH (μ (t + 1)) c → vec t = true
  drop : ∀ t < N, colH (μ (t + 1)) c < colH (μ t) c → vec t = false
  start : 1 ≤ c → colH (μ 0) c = 0
  dual : c ≤ 0 → ∀ t < N, (colH (μ t) c < colH (μ (t + 1)) c → 1 ≤ colH (μ t) c) ∧
    (colH (μ (t + 1)) c < colH (μ t) c → 2 ≤ colH (μ t) c)

end Path

/-! ## The order of the lifted states -/

section Order

variable {A : Type*} [CommRing A] {k p : ℕ} {π : A}

/-- **`π^n ∣ x` gives `π^{n+1} ∣ π·x`.** -/
theorem dvd_pi_mul {n : ℕ} {x : A} (h : π ^ n ∣ x) : π ^ (n + 1) ∣ π * x := by
  rw [pow_succ']
  exact mul_dvd_mul_left π h

/-- **The order invariant of a wedge-type state** (columns `c ≥ 1`) at the line `v`: order `≥ C`, support in degree
`h`, and in positive degree order `≥ C + 1` after wedging with `v`. -/
structure InvW (π : A) (C h : ℕ) (T : Finset (Fin k) → A) (v : Fin k → A) : Prop where
  dvd : ∀ J, π ^ C ∣ T J
  supp : ∀ J, J.card ≠ h → T J = 0
  line : 1 ≤ h → ∀ J, π ^ (C + 1) ∣ wedge v T J

/-- **The order invariant of a contraction-type state** (columns `c ≤ 0`) at the line `v`: order `≥ C`, and order
`≥ C + 1` after contracting with `v`. -/
structure InvC (π : A) (C : ℕ) (T : Finset (Fin k) → A) (v : Fin k → A) : Prop where
  dvd : ∀ J, π ^ C ∣ T J
  line : ∀ J, π ^ (C + 1) ∣ contr v T J

/-- **Wedging a lifted vector letter** `x·v + π·u`: the order grows by one iff the degree is positive. -/
theorem InvW.grow {C h : ℕ} {T : Finset (Fin k) → A} {v : Fin k → A} (hI : InvW π C h T v) (x : A)
    (u : Fin k → A) : InvW π (C + if 1 ≤ h then 1 else 0) (h + 1) (wedge (fun a => x * v a + π * u a) T) v := by
  have e : wedge (fun a => x * v a + π * u a) T = fun J => x * wedge v T J + π * wedge u T J :=
    funext fun J => wedge_lin x π v u T J
  refine ⟨fun J => ?_, fun J hJ => wedge_supp hI.supp _ hJ, fun _ J => ?_⟩
  · rw [e]
    split_ifs with hh
    · exact dvd_add (Dvd.dvd.mul_left (hI.line hh J) _) (dvd_pi_mul (dvd_wedge hI.dvd u J))
    · rw [add_zero]
      exact dvd_add (Dvd.dvd.mul_left (dvd_wedge hI.dvd v J) _) (Dvd.dvd.mul_left (dvd_wedge hI.dvd u J) _)
  · rw [e, wedge_lin_st, wedge_wedge_self, wedge_anti, mul_zero, zero_add, mul_neg, dvd_neg]
    split_ifs with hh
    · exact dvd_pi_mul (dvd_wedge (hI.line hh) u J)
    · exact dvd_pi_mul (dvd_wedge (fun J => dvd_wedge hI.dvd v J) u J)

/-- **Contracting a lifted covector letter** `η` (`π ∣ ⟨η, v⟩`): the order grows by one iff the degree drops to `0`.
-/
theorem InvW.drop {C h : ℕ} {T : Finset (Fin k) → A} {v : Fin k → A} (hI : InvW π C h T v) (hh : 1 ≤ h)
    {η φ : Fin k → A} (hη : π ∣ ∑ a, η a * v a) (hφ : ∑ a, φ a * v a = 1) :
    InvW π (C + if h = 1 then 1 else 0) (h - 1) (contr η T) v := by
  refine ⟨fun J => ?_, fun J hJ => contr_supp hI.supp η (by omega), fun hh' J => ?_⟩
  · split_ifs with h1
    · -- `T = φ ⌟ (v ∧ T) + v ∧ (φ ⌟ T)`, and `φ ⌟ T` has degree `0`
      have eT : T = fun J => 1 * contr φ (wedge v T) J + 1 * wedge v (contr φ T) J := funext fun J => by
        have := contr_wedge φ v T J
        rw [hφ, one_mul] at this
        rw [one_mul, one_mul, this]
      have h0 : ∀ J, contr η (contr φ T) J = 0 := fun J =>
        contr_supp (h := 0) (fun J hJ => contr_supp hI.supp φ (by omega)) η (by omega)
      have h2 := contr_wedge η v (contr φ T) J
      have h3 : wedge v (contr η (contr φ T)) J = 0 := Finset.sum_eq_zero fun a _ => by rw [h0, mul_zero]
      rw [eT, contr_lin_st, one_mul, one_mul]
      rw [h3, add_zero] at h2
      rw [h2]
      exact dvd_add (dvd_contr (fun J => dvd_contr (hI.line hh) φ J) η J)
        (by rw [pow_succ']; exact mul_dvd_mul hη (dvd_contr hI.dvd φ J))
    · rw [add_zero]
      exact dvd_contr hI.dvd η J
  · have hh2 : h ≠ 1 := by omega
    rw [ite_eq_right hh2, add_zero]
    have := contr_wedge η v T J
    rw [show wedge v (contr η T) J = (∑ a, η a * v a) * T J - contr η (wedge v T) J by rw [← this]; ring]
    exact dvd_sub (by rw [pow_succ']; exact mul_dvd_mul hη (hI.dvd J)) (dvd_contr (hI.line hh) η J)

/-- **The Frobenius step of the order invariant**: raising to `p^d` multiplies the order by `p^d` and moves the line
to any `v'` with `v' ≡ v^{p^d} (mod p)`. -/
theorem InvW.frob (hp : p.Prime) (hπ : π ∣ (p : A)) {C h : ℕ} {T : Finset (Fin k) → A} {v : Fin k → A}
    (hI : InvW π C h T v) {v' : Fin k → A} {d : ℕ} (hv : ∀ a, (p : A) ∣ v' a - v a ^ p ^ d) :
    InvW π (p ^ d * C) h (pw (p ^ d) T) v' := by
  have hdvd : ∀ J, π ^ (p ^ d * C) ∣ pw (p ^ d) T J := fun J => by
    rw [pw, mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd (hI.dvd J) _
  refine ⟨hdvd, fun J hJ => by rw [pw, hI.supp J hJ, zero_pow (pow_ne_zero _ hp.ne_zero)], fun hh J => ?_⟩
  have hp1 : π ^ (p ^ d * C + 1) ∣ (p : A) * π ^ (p ^ d * C) := by
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_right hπ _
  have e : wedge v' (pw (p ^ d) T) J =
      wedge (fun a => v' a - v a ^ p ^ d) (pw (p ^ d) T) J + wedge (fun a => v a ^ p ^ d) (pw (p ^ d) T) J := by
    simp only [wedge, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  refine dvd_add (hp1.trans (Finset.dvd_sum fun a _ => ?_)) ?_
  · exact mul_dvd_mul (Dvd.dvd.mul_left (hv a) _) (hdvd _)
  · have h1 := frob_wedge hp hI.dvd v d J
    have h2 : π ^ (p ^ d * C + 1) ∣ wedge v T J ^ p ^ d := by
      have hq : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.pos
      refine (pow_dvd_pow π (?_ : p ^ d * C + 1 ≤ (C + 1) * p ^ d)).trans ?_
      · nlinarith
      · rw [pow_mul]
        exact pow_dvd_pow_of_dvd (hI.line hh J) _
    have := dvd_sub h2 (hp1.trans h1)
    rwa [sub_sub_cancel] at this

/-- **Contracting a lifted vector letter** `x·v + π·u` into a contraction-type state raises the order by one. -/
theorem InvC.grow {C : ℕ} {T : Finset (Fin k) → A} {v : Fin k → A} (hI : InvC π C T v) (x : A) (u : Fin k → A) :
    InvC π (C + 1) (contr (fun a => x * v a + π * u a) T) v := by
  have e : contr (fun a => x * v a + π * u a) T = fun J => x * contr v T J + π * contr u T J :=
    funext fun J => contr_lin x π v u T J
  refine ⟨fun J => ?_, fun J => ?_⟩
  · rw [e]
    exact dvd_add (Dvd.dvd.mul_left (hI.line J) _) (dvd_pi_mul (dvd_contr hI.dvd u J))
  · rw [e, contr_lin_st, contr_contr_self, contr_anti, mul_zero, zero_add, mul_neg, dvd_neg]
    exact dvd_pi_mul (dvd_contr hI.line u J)

/-- **Wedging a lifted covector letter** `η` (`π ∣ ⟨η, v⟩`) into a contraction-type state keeps the order. -/
theorem InvC.drop {C : ℕ} {T : Finset (Fin k) → A} {v : Fin k → A} (hI : InvC π C T v) {η : Fin k → A}
    (hη : π ∣ ∑ a, η a * v a) : InvC π C (wedge η T) v := by
  refine ⟨fun J => dvd_wedge hI.dvd η J, fun J => ?_⟩
  have := contr_wedge v η T J
  rw [show contr v (wedge η T) J = (∑ a, v a * η a) * T J - wedge η (contr v T) J by rw [← this]; ring]
  simp_rw [mul_comm (v _)]
  exact dvd_sub (by rw [pow_succ']; exact mul_dvd_mul hη (hI.dvd J)) (dvd_wedge hI.line η J)

/-- **The Frobenius step of the contraction-type invariant.** -/
theorem InvC.frob (hp : p.Prime) (hπ : π ∣ (p : A)) {C : ℕ} {T : Finset (Fin k) → A} {v : Fin k → A}
    (hI : InvC π C T v) {v' : Fin k → A} {d : ℕ} (hv : ∀ a, (p : A) ∣ v' a - v a ^ p ^ d) :
    InvC π (p ^ d * C) (pw (p ^ d) T) v' := by
  have hdvd : ∀ J, π ^ (p ^ d * C) ∣ pw (p ^ d) T J := fun J => by
    rw [pw, mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd (hI.dvd J) _
  refine ⟨hdvd, fun J => ?_⟩
  have hp1 : π ^ (p ^ d * C + 1) ∣ (p : A) * π ^ (p ^ d * C) := by
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_right hπ _
  have e : contr v' (pw (p ^ d) T) J =
      contr (fun a => v' a - v a ^ p ^ d) (pw (p ^ d) T) J + contr (fun a => v a ^ p ^ d) (pw (p ^ d) T) J := by
    simp only [contr, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  refine dvd_add (hp1.trans (Finset.dvd_sum fun a _ => ?_)) ?_
  · exact mul_dvd_mul (Dvd.dvd.mul_left (hv a) _) (hdvd _)
  · have h1 := frob_contr hp hI.dvd v d J
    have h2 : π ^ (p ^ d * C + 1) ∣ contr v T J ^ p ^ d := by
      have hq : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.pos
      refine (pow_dvd_pow π (?_ : p ^ d * C + 1 ≤ (C + 1) * p ^ d)).trans ?_
      · nlinarith
      · rw [pow_mul]
        exact pow_dvd_pow_of_dvd (hI.line J) _
    have := dvd_sub h2 (hp1.trans h1)
    rwa [sub_sub_cancel] at this

/-- **The line moves by Frobenius**: `v(pos(t + 1)) ≡ v(pos t)^{p^{pos(t + 1) − pos t}} (mod p)`. -/
theorem line_next {v : ℕ → Fin k → A} (hv : ∀ s d a, (p : A) ∣ v (s + d) a - v s a ^ p ^ d) {pos : ℕ → ℕ} {t : ℕ}
    (ht : pos t ≤ pos (t + 1)) (a : Fin k) :
    (p : A) ∣ v (pos (t + 1)) a - v (pos t) a ^ p ^ (pos (t + 1) - pos t) := by
  have := hv (pos t) (pos (t + 1) - pos t) a
  rwa [Nat.add_sub_cancel' ht] at this

/-- **The order of the lifted twisted column states** (the core of T9f(ord)), over any commutative ring `A` with
`π ∣ p`: if the lines `v s` (one per position) satisfy `v(s + d) ≡ v(s)^{p^d} (mod p)` and are unimodular
(`⟨φ s, v s⟩ = 1`), the lifted vector letters are `x·v(pos t) + π·u` and the lifted covector letters `η` have
`π ∣ ⟨η, v(pos t)⟩`, then the twisted state of the lifted letters has order `≥ cost(c)`. -/
theorem ord_core (hp : p.Prime) (hπ : π ∣ (p : A)) {vec : ℕ → Bool} {y v φ : ℕ → Fin k → A} {pos : ℕ → ℕ}
    {μ : ℕ → Fin k → ℤ} {c : ℤ} {N : ℕ} (hpos : ∀ t < N, pos t ≤ pos (t + 1)) (hC : ColCond vec μ c N)
    (hv : ∀ s d a, (p : A) ∣ v (s + d) a - v s a ^ p ^ d) (hφ : ∀ s, ∑ a, φ s a * v s a = 1)
    (hvec : ∀ t < N, vec t = true → ∃ (x : A) (u : Fin k → A), y t = fun a => x * v (pos t) a + π * u a)
    (hcov : ∀ t < N, vec t = false → π ∣ ∑ a, y t a * v (pos t) a) (J : Finset (Fin k)) :
    π ^ cost p pos μ c N ∣ colSt y (colStep μ c) (frobExp p pos) N J := by
  by_cases hc : 1 ≤ c
  · have key : ∀ t ≤ N, InvW π (cost p pos μ c t) (colH (μ t) c) (colSt y (colStep μ c) (frobExp p pos) t)
        (v (pos t)) := by
      intro t ht
      induction t with
      | zero =>
        refine ⟨fun J => by simp [cost], fun J hJ => ?_, fun h => by rw [hC.start hc] at h; omega⟩
        rw [hC.start hc] at hJ
        simp only [colSt, st0]
        rw [ite_eq_right (fun h => hJ (by rw [h, Finset.card_empty]))]
      | succ t ih =>
        have htN : t < N := by omega
        have I := ih (by omega)
        have hv' := line_next hv (hpos t htN)
        rw [colSt_succ, cost_succ hpos μ c htN, frobExp]
        rcases lt_trichotomy (colH (μ t) c) (colH (μ (t + 1)) c) with hlt | heq | hgt
        · have hst : colStep μ c t = .wed := by simp [colStep, hlt, hc]
          have h1 : colH (μ (t + 1)) c = colH (μ t) c + 1 := by have := (hC.step t htN).1; omega
          have hco : (if costly μ c t then 1 else 0) = (if 1 ≤ colH (μ t) c then 1 else 0) := by
            unfold costly
            by_cases h1 : 1 ≤ colH (μ t) c <;> simp [hlt, h1, not_lt.2 hlt.le]
          obtain ⟨x, u, hy⟩ := hvec t htN (hC.grow t htN hlt)
          simp only [hst, Step.app, hy, hco, h1]
          exact (I.grow x u).frob hp hπ hv'
        · have hst : colStep μ c t = .keep := by simp [colStep, heq]
          have hco : (if costly μ c t then 1 else 0) = 0 := by simp [costly, heq]
          simp only [hst, Step.app, hco, add_zero, ← heq]
          exact I.frob hp hπ hv'
        · have hst : colStep μ c t = .con := by simp [colStep, hgt, not_lt.2 hgt.le, hc]
          have h1 : colH (μ (t + 1)) c = colH (μ t) c - 1 := by have := (hC.step t htN).2; omega
          have hco : (if costly μ c t then 1 else 0) = (if colH (μ t) c = 1 then 1 else 0) := by
            unfold costly
            by_cases h1 : colH (μ t) c = 1 <;> simp [hgt, h1, not_lt.2 hgt.le] <;> omega
          simp only [hst, Step.app, hco, h1]
          exact (I.drop (by omega) (hcov t htN (hC.drop t htN hgt)) (hφ _)).frob hp hπ hv'
    exact (key N le_rfl).dvd J
  · have hc0 : c ≤ 0 := by omega
    have key : ∀ t ≤ N, InvC π (cost p pos μ c t) (colSt y (colStep μ c) (frobExp p pos) t) (v (pos t)) := by
      intro t ht
      induction t with
      | zero =>
        refine ⟨fun J => by simp [cost], fun J => ?_⟩
        have h0 : contr (v (pos 0)) (colSt y (colStep μ c) (frobExp p pos) 0) J = 0 :=
          Finset.sum_eq_zero fun a _ => by simp [colSt, st0]
        rw [h0]
        exact dvd_zero _
      | succ t ih =>
        have htN : t < N := by omega
        have I := ih (by omega)
        have hv' := line_next hv (hpos t htN)
        rw [colSt_succ, cost_succ hpos μ c htN, frobExp]
        rcases lt_trichotomy (colH (μ t) c) (colH (μ (t + 1)) c) with hlt | heq | hgt
        · have hst : colStep μ c t = .con := by simp [colStep, hlt, hc]
          have hco : (if costly μ c t then 1 else 0) = 1 := by
            have := ((hC.dual hc0 t htN).1 hlt)
            simp [costly, hlt, this]
          obtain ⟨x, u, hy⟩ := hvec t htN (hC.grow t htN hlt)
          simp only [hst, Step.app, hy, hco]
          exact (I.grow x u).frob hp hπ hv'
        · have hst : colStep μ c t = .keep := by simp [colStep, heq]
          have hco : (if costly μ c t then 1 else 0) = 0 := by simp [costly, heq]
          simp only [hst, Step.app, hco, add_zero]
          exact I.frob hp hπ hv'
        · have hst : colStep μ c t = .wed := by simp [colStep, hgt, not_lt.2 hgt.le, hc]
          have hco : (if costly μ c t then 1 else 0) = 0 := by
            have := ((hC.dual hc0 t htN).2 hgt)
            simp [costly, not_lt.2 hgt.le]
            omega
          simp only [hst, Step.app, hco, add_zero]
          exact (I.drop (hcov t htN (hC.drop t htN hgt))).frob hp hπ hv'
    exact (key N le_rfl).dvd J

end Order

/-! ## The column states as letter polynomials, and their order -/

section Poly

variable (R : Type*) [CommRing R] {k : ℕ}

/-- **The column state** `K_c(J)` (T2) of a path `μ`: the state of the column `c` after `N` letters, the letters being
the variable vectors `X_{t,·}`. -/
def colK (μ : ℕ → Fin k → ℤ) (c : ℤ) (N : ℕ) : Finset (Fin k) → MvPolynomial (ℕ × Fin k) R :=
  colSt (fun t a => X (t, a)) (colStep μ c) (fun _ => 1) N

/-- **The twisted column state** `twCol_c(J)` (T9f): as `K_c`, but after the letter `t` every coordinate is raised to
`p^{pos(t + 1) − pos t}`; the final position `z` is `pos N`. -/
def twCol (p : ℕ) (pos : ℕ → ℕ) (μ : ℕ → Fin k → ℤ) (c : ℤ) (N : ℕ) : Finset (Fin k) → MvPolynomial (ℕ × Fin k) R :=
  colSt (fun t a => X (t, a)) (colStep μ c) (frobExp p pos) N

/-- **(deg)** The twisted column state is homogeneous: of degree `p^{z − pos t}` in each height-changing letter `t`,
and `0` in the other letters. -/
theorem twCol_deg {p : ℕ} {pos : ℕ → ℕ} {N : ℕ} (hpos : ∀ t < N, pos t ≤ pos (t + 1)) (μ : ℕ → Fin k → ℤ) (c : ℤ)
    (J : Finset (Fin k)) :
    IsWeightedHomogeneous (rowW ℕ k) (twCol R p pos μ c N J)
      (fun u => if u < N ∧ colH (μ u) c ≠ colH (μ (u + 1)) c then p ^ (pos N - pos u) else 0) := by
  suffices h : ∀ t ≤ N, ∀ J, IsWeightedHomogeneous (rowW ℕ k)
      (colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin k) R)) (colStep μ c) (frobExp p pos) t J)
      (fun u => if u < t ∧ colH (μ u) c ≠ colH (μ (u + 1)) c then p ^ (pos t - pos u) else 0) from h N le_rfl J
  intro t ht
  induction t with
  | zero =>
    intro J
    have e : (fun u => if u < 0 ∧ colH (μ u) c ≠ colH (μ (u + 1)) c then p ^ (pos 0 - pos u) else 0) = 0 :=
      funext fun u => by simp
    rw [e]
    simp only [colSt, st0]
    split_ifs
    · exact isWeightedHomogeneous_one R _
    · exact isWeightedHomogeneous_zero R _ _
  | succ t ih =>
    intro J
    have htN : t < N := by omega
    set D := fun u => if u < t ∧ colH (μ u) c ≠ colH (μ (u + 1)) c then p ^ (pos t - pos u) else 0 with hDdef
    have hD : (fun u => if u < t + 1 ∧ colH (μ u) c ≠ colH (μ (u + 1)) c then p ^ (pos (t + 1) - pos u) else 0) =
        frobExp p pos t • (D + if colH (μ t) c ≠ colH (μ (t + 1)) c then Pi.single t 1 else 0) := by
      funext u
      have hex : (if colH (μ t) c ≠ colH (μ (t + 1)) c then Pi.single t 1 else (0 : ℕ → ℕ)) u =
          if u = t ∧ colH (μ t) c ≠ colH (μ (t + 1)) c then 1 else 0 := by
        by_cases hu : u = t <;> split_ifs <;> simp_all
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hex, hDdef, frobExp]
      rcases lt_trichotomy u t with hu | rfl | hu
      · have h1 := mono_of_succ hpos hu.le htN.le
        have h2 := hpos t htN
        have e : p ^ (pos (t + 1) - pos u) = p ^ (pos (t + 1) - pos t) * p ^ (pos t - pos u) := by
          rw [← pow_add]
          congr 1
          omega
        by_cases hc : colH (μ u) c ≠ colH (μ (u + 1)) c
        · simp [hu, Nat.lt_succ_of_lt hu, hc, hu.ne, e]
        · simp [hc, hu.ne]
      · simp
      · simp [show ¬u < t + 1 by omega, show ¬u < t by omega, show u ≠ t by omega]
    have hterm : ∀ (J' : Finset (Fin k)) (a : Fin k) (n : ℕ), IsWeightedHomogeneous (rowW ℕ k)
        ((-1) ^ n * X (t, a) * colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin k) R)) (colStep μ c)
          (frobExp p pos) t J') (D + Pi.single t 1) := fun J' a n => by
      have h1 : IsWeightedHomogeneous (rowW ℕ k) ((-1) ^ n : MvPolynomial (ℕ × Fin k) R) 0 := by
        have := ((isWeightedHomogeneous_one R (rowW ℕ k)).neg).pow n
        rwa [smul_zero] at this
      have := (h1.mul (isWeightedHomogeneous_X R (rowW ℕ k) (t, a))).mul (ih (by omega) J')
      rwa [zero_add, add_comm, rowW] at this
    rw [colSt_succ, hD]
    refine IsWeightedHomogeneous.pow ?_ _
    by_cases hc : colH (μ t) c = colH (μ (t + 1)) c
    · rw [colStep_keep hc, ite_eq_right (not_not.2 hc), add_zero]
      exact ih (by omega) J
    · rw [ite_eq_left hc]
      have hw : IsWeightedHomogeneous (rowW ℕ k)
          (wedge (fun a => X (t, a)) (colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin k) R)) (colStep μ c)
            (frobExp p pos) t) J) (D + Pi.single t 1) :=
        IsWeightedHomogeneous.sum _ _ _ fun a _ => hterm _ a _
      have hk : IsWeightedHomogeneous (rowW ℕ k)
          (contr (fun a => X (t, a)) (colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin k) R)) (colStep μ c)
            (frobExp p pos) t) J) (D + Pi.single t 1) :=
        IsWeightedHomogeneous.sum _ _ _ fun a _ => hterm _ a _
      rcases lt_or_gt_of_ne hc with h | h
      · rw [colStep_grow h]
        split_ifs
        · exact hw
        · exact hk
      · rw [colStep_drop h]
        split_ifs
        · exact hk
        · exact hw

end Poly

section Lift

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' m : ℕ}

omit [IsDomain W] [IsDiscreteValuationRing W] [IsDomain O] [IsDiscreteValuationRing O] in
/-- **(int)** The twisted column state has integer coefficients: it is the image of the state over `ℤ`, so it is
`O`-integral. -/
theorem twCol_int (pos : ℕ → ℕ) (μ : ℕ → Fin (m + 1) → ℤ) (c : ℤ) (N : ℕ) (J : Finset (Fin (m + 1))) :
    twCol Kf p pos μ c N J = map (Int.castRingHom Kf) (twCol ℤ p pos μ c N J) ∧ OrdGe ϖ 0 (twCol Kf p pos μ c N J) := by
  have e : twCol Kf p pos μ c N J = map (Int.castRingHom Kf) (twCol ℤ p pos μ c N J) := by
    rw [twCol, twCol, map_colSt]
    simp only [map_X]
  refine ⟨e, fun mm => ⟨(twCol ℤ p pos μ c N J).coeff mm, ?_⟩⟩
  rw [e, coeff_map, pow_zero, one_mul, eq_intCast, map_intCast]

/-- **The lift substitution as an integral substitution**: the lifted letters `ℓ_g(X_{t,a})` are the images of
polynomials over `O`, the lines are the rows `0` of the `σ^s(g⁻¹)`, and the Frobenius moves them. -/
theorem lift_data (hU : Unram p n' W Qq O Kf ι σ j ϖ) (vec : ℕ → Bool) (pos : ℕ → ℕ)
    {g : Matrix (Fin (m + 1)) (Fin (m + 1)) W} (hg : IsUnit g.det) :
    ∃ (y v φ : ℕ → Fin (m + 1) → MvPolynomial (ℕ × Fin (m + 1)) O),
      (∀ t a, map (algebraMap O Kf) (y t a) = liftSub ι σ ϖ 1 vec pos g (X (t, a))) ∧
      (∀ s d a, (p : MvPolynomial (ℕ × Fin (m + 1)) O) ∣ v (s + d) a - v s a ^ p ^ d) ∧
      (∀ s, ∑ a, φ s a * v s a = 1) ∧
      (∀ t, vec t = true → ∃ (x : MvPolynomial (ℕ × Fin (m + 1)) O) (u : Fin (m + 1) → MvPolynomial _ O),
        y t = fun a => x * v (pos t) a + C ϖ * u a) ∧
      (∀ t, vec t = false → C ϖ ∣ ∑ a, y t a * v (pos t) a) := by
  classical
  have := hU.frac_O
  have hinj := IsFractionRing.injective O Kf
  choose oE hoE using fun s (w : W) => hU.exists_map_eq s w
  have htw : ∀ s (M : Matrix (Fin (m + 1)) (Fin (m + 1)) W) a b, twK ι σ s M a b = algebraMap O Kf (oE s (M a b)) :=
    fun s M a b => hoE s (M a b)
  have hprod : ∀ s i b, ∑ a, oE s (g⁻¹ i a) * oE s (g a b) = if i = b then 1 else 0 := fun s i b => by
    apply hinj
    have := congrFun (congrFun (twK_inv_mul (ι := ι) (σ := σ) s hg).1 i) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [htw] at this
    rw [map_sum]
    simp only [map_mul, this]
    split_ifs <;> simp
  have hfrob : ∀ s d (w : W), ∃ o, oE (s + d) w = oE s w ^ p ^ d + p * o := fun s d w => by
    obtain ⟨y, hy⟩ := frob_pow hU d w
    obtain ⟨o, ho⟩ := hU.exists_map_eq s y
    refine ⟨o, hinj ?_⟩
    rw [← hoE, map_add, map_mul, map_pow, map_natCast, ← hoE, ← ho, pow_add]
    show ι ((σ ^ s) ((σ ^ d) (algebraMap W Qq w))) = _
    rw [hy]
    simp only [map_add, map_mul, map_pow, map_natCast]
  let sc : ℕ → Fin (m + 1) → O := fun t b => if scaled 1 vec (t, b) then ϖ else 1
  refine ⟨fun t a => ∑ b, C (sc t b * if vec t then oE (pos t) (g⁻¹ b a) else oE (pos t) (g a b)) * X (t, b),
    fun s a => C (oE s (g⁻¹ 0 a)), fun s a => C (oE s (g a 0)), fun t a => ?_, fun s d a => ?_, fun s => ?_,
    fun t ht => ?_, fun t ht => ?_⟩
  · rw [liftSub, aeval_X, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, map_C, map_X, sc, htw, apply_ite (algebraMap O Kf), map_one]
  · obtain ⟨o, ho⟩ := hfrob s d (g⁻¹ 0 a)
    refine ⟨C o, ?_⟩
    show C (oE (s + d) (g⁻¹ 0 a)) - C (oE s (g⁻¹ 0 a)) ^ p ^ d = _
    rw [ho, map_add, map_pow, map_mul, map_natCast]
    ring
  · show ∑ a, C (oE s (g a 0)) * C (oE s (g⁻¹ 0 a)) = 1
    simp_rw [← map_mul, mul_comm (oE s (g _ 0))]
    rw [← map_sum, hprod]
    simp
  · refine ⟨X (t, 0), fun a => ∑ b : Fin m, C (oE (pos t) (g⁻¹ b.succ a)) * X (t, b.succ), funext fun a => ?_⟩
    show ∑ b, C (sc t b * if vec t = true then oE (pos t) (g⁻¹ b a) else oE (pos t) (g a b)) * X (t, b) =
      X (t, 0) * C (oE (pos t) (g⁻¹ 0 a)) + C ϖ * ∑ b : Fin m, C (oE (pos t) (g⁻¹ b.succ a)) * X (t, b.succ)
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    simp only [sc, scaled, ht, ite_true, Fin.val_zero, Fin.val_succ]
    congr 1
    · simp [mul_comm]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp only [show 1 ≤ b.val + 1 by omega, decide_true, ite_true, map_mul]
      ring
  · have e : ∑ a, (∑ b, C (sc t b * if vec t then oE (pos t) (g⁻¹ b a) else oE (pos t) (g a b)) * X (t, b)) *
        C (oE (pos t) (g⁻¹ 0 a)) = ∑ b, C (sc t b) * X (t, b) * C (if (0 : Fin (m + 1)) = b then 1 else 0) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hprod, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [ht, Bool.false_eq_true, ite_false, map_mul]
      ring
    rw [e]
    refine Finset.dvd_sum fun b _ => ?_
    split_ifs with hb
    · subst hb
      simp only [sc, scaled, ht, Bool.false_eq_true, ite_false, Fin.val_zero, Nat.lt_one_iff, decide_true, ite_true]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
    · rw [map_zero, mul_zero]
      exact dvd_zero _

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`(C ϖ)^i ∣ F` over `O` gives order `≥ i` over `Kf`.** -/
theorem ordGe_map {τ : Type*} {i : ℕ} {F : MvPolynomial τ O} (h : C ϖ ^ i ∣ F) :
    OrdGe ϖ i (map (algebraMap O Kf) F) := by
  obtain ⟨G, rfl⟩ := h
  intro mm
  refine ⟨G.coeff mm, ?_⟩
  rw [coeff_map, ← C_pow, coeff_C_mul]

/-- **(ord)** For every `g ∈ GL_k(W)` the lift of the twisted column state has order `≥ cost(c)`:
`Dvd ϖ (cost c) (ℓ_g (twCol_c J))`. (Strictness is not needed here.) -/
theorem twCol_ord (hU : Unram p n' W Qq O Kf ι σ j ϖ) {vec : ℕ → Bool} {pos : ℕ → ℕ} {μ : ℕ → Fin (m + 1) → ℤ}
    {c : ℤ} {N : ℕ} (hpos : ∀ t < N, pos t ≤ pos (t + 1)) (hC : ColCond vec μ c N)
    {g : Matrix (Fin (m + 1)) (Fin (m + 1)) W} (hg : IsUnit g.det) (J : Finset (Fin (m + 1))) :
    OrdGe ϖ (cost p pos μ c N) (liftSub ι σ ϖ 1 vec pos g (twCol Kf p pos μ c N J)) := by
  obtain ⟨y, v, φ, hlift, hv, hφ, hvec, hcov⟩ := lift_data hU vec pos hg
  have e : liftSub ι σ ϖ 1 vec pos g (twCol Kf p pos μ c N J) =
      map (algebraMap O Kf) (colSt y (colStep μ c) (frobExp p pos) N J) := by
    rw [twCol, ← AlgHom.coe_toRingHom, map_colSt, map_colSt]
    simp only [AlgHom.coe_toRingHom, hlift]
  have hπ : C ϖ ∣ (p : MvPolynomial (ℕ × Fin (m + 1)) O) :=
    ⟨C ϖ, by rw [← map_natCast C, ← hU.sq, map_pow, sq]⟩
  rw [e]
  exact ordGe_map (ord_core hU.prime hπ hpos hC hv hφ (fun t _ => hvec t) (fun t _ => hcov t) J)

end Lift

/-! ## The plane/tangent split of coordinate sets -/

section Split

variable {A : Type*} [CommRing A] {m : ℕ}

/-- **The plane part** of a set of coordinates: `univ ⊆ Fin 1` if `0 ∈ J`, else `∅`. -/
def pl0 (J : Finset (Fin (m + 1))) : Finset (Fin 1) := if (0 : Fin (m + 1)) ∈ J then univ else ∅

/-- **The tangent part** of a set of coordinates: `{b : b + 1 ∈ J}`. -/
def tanPart (J : Finset (Fin (m + 1))) : Finset (Fin m) := univ.filter fun b => b.succ ∈ J

/-- **Membership in the tangent part.** -/
theorem mem_tanPart {J : Finset (Fin (m + 1))} {b : Fin m} : b ∈ tanPart J ↔ b.succ ∈ J := by
  simp [tanPart]

/-- **A sum over `J`**, split into the plane coordinate and the tangent part. -/
theorem sum_split (J : Finset (Fin (m + 1))) (f : Fin (m + 1) → A) :
    ∑ a ∈ J, f a = (if (0 : Fin (m + 1)) ∈ J then f 0 else 0) + ∑ b ∈ tanPart J, f b.succ := by
  have e : ∑ a ∈ J, f a = ∑ a, if a ∈ J then f a else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext
    simp
  rw [e, Fin.sum_univ_succ, tanPart, Finset.sum_filter]

/-- **A sum over the complement of `J`**, split into the plane coordinate and the tangent part. -/
theorem sum_split_compl (J : Finset (Fin (m + 1))) (f : Fin (m + 1) → A) :
    ∑ a ∈ Jᶜ, f a = (if (0 : Fin (m + 1)) ∈ J then 0 else f 0) + ∑ b ∈ (tanPart J)ᶜ, f b.succ := by
  have e : ∑ a ∈ Jᶜ, f a = ∑ a, if a ∈ J then 0 else f a := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    congr 1
    ext
    simp
  have e2 : ∑ b ∈ (tanPart J)ᶜ, f b.succ = ∑ b : Fin m, if b.succ ∈ J then 0 else f b.succ := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    congr 1
    ext
    simp [mem_tanPart]
  rw [e, Fin.sum_univ_succ, e2]

/-- **The sign of a tangent coordinate** is its sign in the tangent part. -/
theorem sg_succ (b : Fin m) (J : Finset (Fin (m + 1))) : (sg b.succ J : A) = sg b (tanPart J) := by
  unfold sg
  congr 1
  rw [← Finset.card_map (Fin.succEmb m)]
  congr 1
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp [mem_tanPart, Fin.succ_lt_succ_iff]

/-- **The sign of the plane coordinate**: `(−1)^{|tangent part|}`. -/
theorem sg_zero (J : Finset (Fin (m + 1))) : (sg 0 J : A) = (-1) ^ (tanPart J).card := by
  unfold sg
  congr 1
  rw [← Finset.card_map (Fin.succEmb m)]
  congr 1
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp [mem_tanPart, Fin.succ_pos]

/-- **Removing a tangent coordinate** from the tangent part. -/
theorem tanPart_erase_succ (J : Finset (Fin (m + 1))) (b : Fin m) :
    tanPart (J.erase b.succ) = (tanPart J).erase b := by
  ext i
  simp [mem_tanPart, Fin.succ_inj]

/-- **Removing the plane coordinate** keeps the tangent part. -/
theorem tanPart_erase_zero (J : Finset (Fin (m + 1))) : tanPart (J.erase 0) = tanPart J := by
  ext i
  simp [mem_tanPart, Fin.succ_ne_zero]

/-- **Adding a tangent coordinate** to the tangent part. -/
theorem tanPart_insert_succ (J : Finset (Fin (m + 1))) (b : Fin m) :
    tanPart (insert b.succ J) = insert b (tanPart J) := by
  ext i
  simp [mem_tanPart, Fin.succ_inj]

/-- **Removing the plane coordinate** empties the plane part. -/
theorem pl0_erase_zero (J : Finset (Fin (m + 1))) : pl0 (J.erase 0) = ∅ := by
  simp [pl0]

/-- **Removing a tangent coordinate** keeps the plane part. -/
theorem pl0_erase_succ (J : Finset (Fin (m + 1))) (b : Fin m) : pl0 (J.erase b.succ) = pl0 J := by
  simp [pl0, (Fin.succ_ne_zero b).symm]

/-- **Adding a tangent coordinate** keeps the plane part. -/
theorem pl0_insert_succ (J : Finset (Fin (m + 1))) (b : Fin m) : pl0 (insert b.succ J) = pl0 J := by
  simp [pl0, (Fin.succ_ne_zero b).symm]

/-- **The empty set** has empty plane and tangent parts, and conversely. -/
theorem eq_empty_iff_split {J : Finset (Fin (m + 1))} : J = ∅ ↔ (0 : Fin (m + 1)) ∉ J ∧ tanPart J = ∅ := by
  refine ⟨fun h => by simp [h, tanPart], fun ⟨h0, ht⟩ => Finset.eq_empty_of_forall_notMem fun a ha => ?_⟩
  refine Fin.cases (fun h => h0 h) (fun b hb => ?_) a ha
  have : b ∈ tanPart J := mem_tanPart.2 hb
  rw [ht] at this
  simp at this

/-- **The wedge, split** into the plane coordinate and the tangent coordinates. -/
theorem wedge_split (y : Fin (m + 1) → A) (T : Finset (Fin (m + 1)) → A) (J : Finset (Fin (m + 1))) :
    wedge y T J = (if (0 : Fin (m + 1)) ∈ J then sg 0 J * y 0 * T (J.erase 0) else 0) +
      ∑ b ∈ tanPart J, sg b (tanPart J) * y b.succ * T (J.erase b.succ) := by
  rw [wedge, sum_split]
  simp_rw [sg_succ]

/-- **The contraction, split** into the plane coordinate and the tangent coordinates. -/
theorem contr_split (y : Fin (m + 1) → A) (T : Finset (Fin (m + 1)) → A) (J : Finset (Fin (m + 1))) :
    contr y T J = (if (0 : Fin (m + 1)) ∈ J then 0 else sg 0 J * y 0 * T (insert 0 J)) +
      ∑ b ∈ (tanPart J)ᶜ, sg b (tanPart J) * y b.succ * T (insert b.succ J) := by
  rw [contr, sum_split_compl]
  simp_rw [sg_succ]

/-- **The wedge on `Fin 1`** at `univ`. -/
theorem wedge_one_univ (z : Fin 1 → A) (P : Finset (Fin 1) → A) : wedge z P univ = z 0 * P ∅ := by
  rw [wedge, Finset.univ_unique, Finset.sum_singleton]
  simp [sg, Finset.filter_singleton]

end Split

/-! ## The leading term at the identity -/

section Lead

variable {A : Type*} [CommRing A] {m : ℕ} {π : A}

/-- **The leading-term invariant of a joined state, columns `c ≥ 1`**: `T ≡ π^C·Pl(J ∩ 0)·Tan(J ∖ 0)
(mod π^{C+1})`; off the plane (`0 ∉ J`, and `J ≠ ∅` before the plane box `ph`) `T` has order `≥ C + 1`, and `≥ C + 2`
when fresh (a Frobenius power since the last height change); after the plane box `Pl(∅) = 0`. -/
structure InvL (π : A) (C : ℕ) (ph fr : Prop) (T : Finset (Fin (m + 1)) → A) (Pl : Finset (Fin 1) → A)
    (Tan : Finset (Fin m) → A) : Prop where
  pl : ph → Pl ∅ = 0
  lead : ∀ J, π ^ (C + 1) ∣ T J - π ^ C * (Pl (pl0 J) * Tan (tanPart J))
  off : ∀ J, (0 : Fin (m + 1)) ∉ J → (J ≠ ∅ ∨ ph) → π ^ (C + 1) ∣ T J
  fresh : fr → ∀ J, (0 : Fin (m + 1)) ∉ J → (J ≠ ∅ ∨ ph) → π ^ (C + 2) ∣ T J

/-- **The leading-term invariant of a joined state, columns `c ≤ 0`** (the plane state is `[∅]`):
`T ≡ π^C·[0 ∉ J]·Tan(J ∖ 0) (mod π^{C+1})`, and for `0 ∈ J` order `≥ C + 1`, `≥ C + 2` when fresh. -/
structure InvD (π : A) (C : ℕ) (fr : Prop) (T : Finset (Fin (m + 1)) → A) (Tan : Finset (Fin m) → A) : Prop where
  lead : ∀ J, π ^ (C + 1) ∣ T J - π ^ C * (st0 (pl0 J) * Tan (tanPart J))
  off : ∀ J, (0 : Fin (m + 1)) ∈ J → π ^ (C + 1) ∣ T J
  fresh : fr → ∀ J, (0 : Fin (m + 1)) ∈ J → π ^ (C + 2) ∣ T J

/-- **A congruence `x ≡ π^C·L (mod π^{C+1})` gives `π^C ∣ x`.** -/
theorem dvd_of_lead {C : ℕ} {x L : A} (h : π ^ (C + 1) ∣ x - π ^ C * L) : π ^ C ∣ x := by
  have e : x = (x - π ^ C * L) + π ^ C * L := by ring
  rw [e]
  exact dvd_add ((pow_dvd_pow π (Nat.le_succ C)).trans h) (dvd_mul_right _ _)

/-- **Powers of a congruence**: `x ≡ π^C·L (mod π^{C+1})` gives `x^q ≡ π^{qC}·L^q (mod π^{qC+1})`. -/
theorem lead_pow {C : ℕ} {x L : A} (h : π ^ (C + 1) ∣ x - π ^ C * L) (q : ℕ) :
    π ^ (q * C + 1) ∣ x ^ q - π ^ (q * C) * L ^ q := by
  obtain ⟨r, hr⟩ := h
  have hx : x = π ^ C * (L + π * r) := by linear_combination hr
  have h1 : π ∣ (L + π * r) ^ q - L ^ q := by
    have := sub_dvd_pow_sub_pow (L + π * r) L q
    rw [add_sub_cancel_left] at this
    exact (dvd_mul_right π r).trans this
  rw [hx, mul_pow, ← pow_mul, mul_comm C q, ← mul_sub, pow_succ]
  exact mul_dvd_mul_left _ h1

/-- **Orders of powers**: `π^n ∣ x` gives `π^e ∣ x^q` for `e ≤ q·n`. -/
theorem pow_dvd_of {n e : ℕ} {x : A} (h : π ^ n ∣ x) {q : ℕ} (he : e ≤ q * n) : π ^ e ∣ x ^ q :=
  (pow_dvd_pow π he).trans (by rw [pow_mul']; exact pow_dvd_pow_of_dvd h q)

/-- **Weakening the flags** of the invariant. -/
theorem InvL.mono {C C' : ℕ} {ph ph' fr fr' : Prop} {T : Finset (Fin (m + 1)) → A} {Pl : Finset (Fin 1) → A}
    {Tan : Finset (Fin m) → A} (I : InvL π C ph fr T Pl Tan) (hC : C' = C) (hph : ph' ↔ ph) (hfr : fr' → fr) :
    InvL π C' ph' fr' T Pl Tan := by
  subst hC
  exact ⟨fun h => I.pl (hph.1 h), I.lead, fun J h0 hJ => I.off J h0 (hJ.imp_right hph.1),
    fun h J h0 hJ => I.fresh (hfr h) J h0 (hJ.imp_right hph.1)⟩

/-- **The Frobenius power of the invariant**: the order is multiplied by `q`, and a power `q ≥ 2` makes it fresh. -/
theorem InvL.pow {C : ℕ} {ph fr : Prop} {T : Finset (Fin (m + 1)) → A} {Pl : Finset (Fin 1) → A}
    {Tan : Finset (Fin m) → A} (I : InvL π C ph fr T Pl Tan) {q : ℕ} (hq : 1 ≤ q) :
    InvL π (q * C) ph (fr ∨ 2 ≤ q) (pw q T) (pw q Pl) (pw q Tan) := by
  refine ⟨fun h => by rw [pw, I.pl h, zero_pow (by omega)], fun J => ?_, fun J h0 hJ => ?_, ?_⟩
  · have := lead_pow (I.lead J) q
    rwa [mul_pow] at this
  · exact pow_dvd_of (I.off J h0 hJ) (by rw [Nat.mul_succ]; omega)
  · rintro (h | h) J h0 hJ
    · exact pow_dvd_of (I.fresh h J h0 hJ) (by rw [show q * (C + 2) = q * C + 2 * q by ring]; omega)
    · exact pow_dvd_of (I.off J h0 hJ) (by rw [Nat.mul_succ]; omega)

/-- **The plane box** (columns `c ≥ 1`): wedging the vector letter `(x₀, π·x_tan)` before the plane box. -/
theorem InvL.plane {C : ℕ} {fr : Prop} {T : Finset (Fin (m + 1)) → A} {Pl : Finset (Fin 1) → A}
    {Tan : Finset (Fin m) → A} (I : InvL π C False fr T Pl Tan) {y : Fin (m + 1) → A} {x0 : A} {xs : Fin m → A}
    (hy0 : y 0 = x0) (hys : ∀ b, y b.succ = π * xs b) :
    InvL π C True False (wedge y T) (wedge (fun _ => x0) Pl) Tan := by
  have hdvd : ∀ J, π ^ C ∣ T J := fun J => dvd_of_lead (I.lead J)
  have hS : ∀ J : Finset (Fin (m + 1)),
      π ^ (C + 1) ∣ ∑ b ∈ tanPart J, sg b (tanPart J) * y b.succ * T (J.erase b.succ) := fun J =>
    Finset.dvd_sum fun b _ => by
      rw [hys, show sg b (tanPart J) * (π * xs b) * T (J.erase b.succ) =
        π * (sg b (tanPart J) * xs b * T (J.erase b.succ)) by ring]
      exact dvd_pi_mul (Dvd.dvd.mul_left (hdvd _) _)
  have hP0 : wedge (fun _ => x0) Pl ∅ = 0 := by simp [wedge]
  refine ⟨fun _ => hP0, fun J => ?_, fun J h0 _ => ?_, fun h => h.elim⟩
  · rw [wedge_split, hy0]
    by_cases h0 : (0 : Fin (m + 1)) ∈ J
    · rw [ite_eq_left h0, show pl0 J = univ from ite_eq_left h0, wedge_one_univ]
      have hl := I.lead (J.erase 0)
      rw [pl0_erase_zero, tanPart_erase_zero] at hl
      set S := ∑ b ∈ tanPart J, sg b (tanPart J) * y b.succ * T (J.erase b.succ)
      by_cases ht : tanPart J = ∅
      · rw [sg_zero, ht, Finset.card_empty, pow_zero]
        rw [ht] at hl
        rw [show 1 * x0 * T (J.erase 0) + S - π ^ C * (x0 * Pl ∅ * Tan ∅) =
          x0 * (T (J.erase 0) - π ^ C * (Pl ∅ * Tan ∅)) + S by ring]
        exact dvd_add (Dvd.dvd.mul_left hl _) (hS J)
      · have hne : J.erase 0 ≠ ∅ := fun h => ht (by rw [← tanPart_erase_zero, h]; simp [tanPart])
        have hoff := I.off (J.erase 0) (Finset.notMem_erase 0 J) (Or.inl hne)
        have h2 : π ^ (C + 1) ∣ π ^ C * (Pl ∅ * Tan (tanPart J)) := by
          have := dvd_sub hoff hl
          rwa [sub_sub_cancel] at this
        rw [show sg 0 J * x0 * T (J.erase 0) + S - π ^ C * (x0 * Pl ∅ * Tan (tanPart J)) =
          sg 0 J * x0 * T (J.erase 0) + S - x0 * (π ^ C * (Pl ∅ * Tan (tanPart J))) by ring]
        exact dvd_sub (dvd_add (Dvd.dvd.mul_left hoff _) (hS J)) (Dvd.dvd.mul_left h2 _)
    · rw [ite_eq_right h0, show pl0 J = ∅ from ite_eq_right h0, hP0, zero_add, zero_mul, mul_zero, sub_zero]
      exact hS J
  · rw [wedge_split, ite_eq_right h0, zero_add]
    exact hS J

/-- **A tangent box from a vector letter** (columns `c ≥ 1`, after the plane box, fresh): the order grows by one and
the leading term is the tangent wedge. -/
theorem InvL.tgrow {C : ℕ} {T : Finset (Fin (m + 1)) → A} {Pl : Finset (Fin 1) → A} {Tan : Finset (Fin m) → A}
    (I : InvL π C True True T Pl Tan) {y : Fin (m + 1) → A} {x0 : A} {xs : Fin m → A} (hy0 : y 0 = x0)
    (hys : ∀ b, y b.succ = π * xs b) : InvL π (C + 1) True False (wedge y T) Pl (wedge xs Tan) := by
  have hfr : ∀ J, (0 : Fin (m + 1)) ∉ J → π ^ (C + 2) ∣ T J := fun J h0 => I.fresh trivial J h0 (Or.inr trivial)
  have hS : ∀ J : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∉ J →
      π ^ (C + 1 + 1) ∣ ∑ b ∈ tanPart J, sg b (tanPart J) * y b.succ * T (J.erase b.succ) := fun J h0 =>
    Finset.dvd_sum fun b _ => by
      rw [hys, show sg b (tanPart J) * (π * xs b) * T (J.erase b.succ) =
        π * (sg b (tanPart J) * xs b * T (J.erase b.succ)) by ring]
      refine dvd_pi_mul (Dvd.dvd.mul_left ((pow_dvd_pow π (by omega)).trans (hfr _ ?_)) _)
      exact fun h => h0 (Finset.mem_of_mem_erase h)
  refine ⟨I.pl, fun J => ?_, fun J h0 _ => ?_, fun h => h.elim⟩
  · rw [wedge_split, hy0]
    by_cases h0 : (0 : Fin (m + 1)) ∈ J
    · rw [ite_eq_left h0, show pl0 J = univ from ite_eq_left h0, wedge, Finset.mul_sum, Finset.mul_sum, add_sub_assoc,
        ← Finset.sum_sub_distrib]
      refine dvd_add (Dvd.dvd.mul_left ((hfr _ (Finset.notMem_erase 0 J))) _) (Finset.dvd_sum fun b _ => ?_)
      have hl := I.lead (J.erase b.succ)
      rw [pl0_erase_succ, show pl0 J = univ from ite_eq_left h0, tanPart_erase_succ] at hl
      rw [hys, show sg b (tanPart J) * (π * xs b) * T (J.erase b.succ) - π ^ (C + 1) * (Pl univ *
        (sg b (tanPart J) * xs b * Tan ((tanPart J).erase b))) = π * (sg b (tanPart J) * xs b *
        (T (J.erase b.succ) - π ^ C * (Pl univ * Tan ((tanPart J).erase b)))) by ring]
      exact dvd_pi_mul (Dvd.dvd.mul_left hl _)
    · rw [ite_eq_right h0, show pl0 J = ∅ from ite_eq_right h0, I.pl trivial, zero_add, zero_mul, mul_zero, sub_zero]
      exact hS J h0
  · rw [wedge_split, ite_eq_right h0, zero_add]
    exact hS J h0

/-- **A tangent box removed by a covector letter** (columns `c ≥ 1`, after the plane box): the order is kept and the
leading term is the tangent contraction. -/
theorem InvL.tdrop {C : ℕ} {fr : Prop} {T : Finset (Fin (m + 1)) → A} {Pl : Finset (Fin 1) → A}
    {Tan : Finset (Fin m) → A} (I : InvL π C True fr T Pl Tan) {y : Fin (m + 1) → A} {x0 : A} {xs : Fin m → A}
    (hy0 : y 0 = π * x0) (hys : ∀ b, y b.succ = xs b) :
    InvL π C True False (contr y T) Pl (contr xs Tan) := by
  have hoff : ∀ J : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∉ J → π ^ (C + 1) ∣ contr y T J := fun J h0 => by
    rw [contr_split, ite_eq_right h0, hy0]
    refine dvd_add ?_ (Finset.dvd_sum fun b _ => ?_)
    · rw [show sg 0 J * (π * x0) * T (insert 0 J) = π * (sg 0 J * x0 * T (insert 0 J)) by ring]
      exact dvd_pi_mul (Dvd.dvd.mul_left (dvd_of_lead (I.lead _)) _)
    · rw [hys]
      refine Dvd.dvd.mul_left (I.off _ ?_ (Or.inr trivial)) _
      simp [h0, (Fin.succ_ne_zero b).symm]
  refine ⟨I.pl, fun J => ?_, fun J h0 _ => hoff J h0, fun h => h.elim⟩
  by_cases h0 : (0 : Fin (m + 1)) ∈ J
  · rw [contr_split, ite_eq_left h0, zero_add, show pl0 J = univ from ite_eq_left h0, contr, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    have hl := I.lead (insert b.succ J)
    rw [pl0_insert_succ, show pl0 J = univ from ite_eq_left h0, tanPart_insert_succ] at hl
    rw [hys, show sg b (tanPart J) * xs b * T (insert b.succ J) - π ^ C * (Pl univ *
      (sg b (tanPart J) * xs b * Tan (insert b (tanPart J)))) = sg b (tanPart J) * xs b *
      (T (insert b.succ J) - π ^ C * (Pl univ * Tan (insert b (tanPart J)))) by ring]
    exact Dvd.dvd.mul_left hl _
  · rw [show pl0 J = ∅ from ite_eq_right h0, I.pl trivial, zero_mul, mul_zero, sub_zero]
    exact hoff J h0

/-- **`[∅]` is idempotent under powers.** -/
theorem st0_pow {k : ℕ} (I : Finset (Fin k)) {q : ℕ} (hq : q ≠ 0) : (st0 I : A) ^ q = st0 I := by
  unfold st0
  split_ifs <;> simp [hq]

/-- **`[∅]` at the plane part** of a set containing `0`. -/
theorem st0_pl0_mem {J : Finset (Fin (m + 1))} (h0 : (0 : Fin (m + 1)) ∈ J) : (st0 (pl0 J) : A) = 0 := by
  simp [st0, pl0, h0]

/-- **`[∅]` at the plane part** of a set avoiding `0`. -/
theorem st0_pl0_notMem {J : Finset (Fin (m + 1))} (h0 : (0 : Fin (m + 1)) ∉ J) : (st0 (pl0 J) : A) = 1 := by
  simp [st0, pl0, h0]

/-- **Weakening the freshness flag** of the dual invariant. -/
theorem InvD.mono {C C' : ℕ} {fr fr' : Prop} {T : Finset (Fin (m + 1)) → A} {Tan : Finset (Fin m) → A}
    (I : InvD π C fr T Tan) (hC : C' = C) (hfr : fr' → fr) : InvD π C' fr' T Tan := by
  subst hC
  exact ⟨I.lead, I.off, fun h => I.fresh (hfr h)⟩

/-- **The Frobenius power of the dual invariant.** -/
theorem InvD.pow {C : ℕ} {fr : Prop} {T : Finset (Fin (m + 1)) → A} {Tan : Finset (Fin m) → A}
    (I : InvD π C fr T Tan) {q : ℕ} (hq : 1 ≤ q) : InvD π (q * C) (fr ∨ 2 ≤ q) (pw q T) (pw q Tan) := by
  refine ⟨fun J => ?_, fun J h0 => ?_, ?_⟩
  · have := lead_pow (I.lead J) q
    rwa [mul_pow, st0_pow _ (by omega)] at this
  · exact pow_dvd_of (I.off J h0) (by rw [Nat.mul_succ]; omega)
  · rintro (h | h) J h0
    · exact pow_dvd_of (I.fresh h J h0) (by rw [show q * (C + 2) = q * C + 2 * q by ring]; omega)
    · exact pow_dvd_of (I.off J h0) (by rw [Nat.mul_succ]; omega)

/-- **A tangent box removed by a covector letter** (columns `c ≤ 0`, a wedge): the order is kept. -/
theorem InvD.tdrop {C : ℕ} {fr : Prop} {T : Finset (Fin (m + 1)) → A} {Tan : Finset (Fin m) → A}
    (I : InvD π C fr T Tan) {y : Fin (m + 1) → A} {x0 : A} {xs : Fin m → A} (hy0 : y 0 = π * x0)
    (hys : ∀ b, y b.succ = xs b) : InvD π C False (wedge y T) (wedge xs Tan) := by
  have hoff : ∀ J : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∈ J → π ^ (C + 1) ∣ wedge y T J := fun J h0 => by
    rw [wedge_split, ite_eq_left h0, hy0]
    refine dvd_add ?_ (Finset.dvd_sum fun b _ => ?_)
    · rw [show sg 0 J * (π * x0) * T (J.erase 0) = π * (sg 0 J * x0 * T (J.erase 0)) by ring]
      exact dvd_pi_mul (Dvd.dvd.mul_left (dvd_of_lead (I.lead _)) _)
    · rw [hys]
      exact Dvd.dvd.mul_left (I.off _ (Finset.mem_erase.2 ⟨(Fin.succ_ne_zero b).symm, h0⟩)) _
  refine ⟨fun J => ?_, hoff, fun h => h.elim⟩
  by_cases h0 : (0 : Fin (m + 1)) ∈ J
  · rw [st0_pl0_mem h0, zero_mul, mul_zero, sub_zero]
    exact hoff J h0
  · rw [wedge_split, ite_eq_right h0, zero_add, st0_pl0_notMem h0, one_mul, wedge, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    have hl := I.lead (J.erase b.succ)
    rw [pl0_erase_succ, st0_pl0_notMem h0, one_mul, tanPart_erase_succ] at hl
    rw [hys, show sg b (tanPart J) * xs b * T (J.erase b.succ) - π ^ C * (sg b (tanPart J) * xs b *
      Tan ((tanPart J).erase b)) = sg b (tanPart J) * xs b * (T (J.erase b.succ) - π ^ C *
      Tan ((tanPart J).erase b)) by ring]
    exact Dvd.dvd.mul_left hl _

/-- **A tangent box from a vector letter** (columns `c ≤ 0`, a contraction, fresh): the order grows by one. -/
theorem InvD.tgrow {C : ℕ} {T : Finset (Fin (m + 1)) → A} {Tan : Finset (Fin m) → A} (I : InvD π C True T Tan)
    {y : Fin (m + 1) → A} {x0 : A} {xs : Fin m → A} (hy0 : y 0 = x0) (hys : ∀ b, y b.succ = π * xs b) :
    InvD π (C + 1) False (contr y T) (contr xs Tan) := by
  have hoff : ∀ J : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∈ J → π ^ (C + 1 + 1) ∣ contr y T J := fun J h0 => by
    rw [contr_split, ite_eq_left h0, zero_add]
    refine Finset.dvd_sum fun b _ => ?_
    rw [hys, show sg b (tanPart J) * (π * xs b) * T (insert b.succ J) =
      π * (sg b (tanPart J) * xs b * T (insert b.succ J)) by ring]
    exact dvd_pi_mul (Dvd.dvd.mul_left (I.off _ (Finset.mem_insert_of_mem h0)) _)
  refine ⟨fun J => ?_, hoff, fun h => h.elim⟩
  by_cases h0 : (0 : Fin (m + 1)) ∈ J
  · rw [st0_pl0_mem h0, zero_mul, mul_zero, sub_zero]
    exact hoff J h0
  · rw [contr_split, ite_eq_right h0, hy0, st0_pl0_notMem h0, one_mul, contr, Finset.mul_sum, add_sub_assoc,
      ← Finset.sum_sub_distrib]
    refine dvd_add (Dvd.dvd.mul_left (I.fresh trivial _ (Finset.mem_insert_self 0 J)) _)
      (Finset.dvd_sum fun b _ => ?_)
    have hl := I.lead (insert b.succ J)
    rw [pl0_insert_succ, st0_pl0_notMem h0, one_mul, tanPart_insert_succ] at hl
    rw [hys, show sg b (tanPart J) * (π * xs b) * T (insert b.succ J) - π ^ (C + 1) * (sg b (tanPart J) * xs b *
      Tan (insert b (tanPart J))) = π * (sg b (tanPart J) * xs b * (T (insert b.succ J) - π ^ C *
      Tan (insert b (tanPart J)))) by ring]
    exact dvd_pi_mul (Dvd.dvd.mul_left hl _)

end Lead

/-! ## Joined paths and the congruence at the identity -/

section Join

variable {m : ℕ}

/-- **The joined path** `t ↦ (ν t, κ t)`: the plane row `ν` (coordinate `0`) and the tangent rows `κ`. -/
def joinPath (ν : ℕ → ℤ) (κ : ℕ → Fin m → ℤ) : ℕ → Fin (m + 1) → ℤ := fun t => Fin.cons (ν t) (κ t)

/-- **The plane path** `t ↦ (ν t)`, in one coordinate. -/
def planePath (ν : ℕ → ℤ) : ℕ → Fin 1 → ℤ := fun t _ => ν t

/-- **The plane height** of the column `c`: `[c ≤ ν t]`. -/
theorem colH_plane (ν : ℕ → ℤ) (t : ℕ) (c : ℤ) : colH (planePath ν t) c = if c ≤ ν t then 1 else 0 := by
  unfold colH planePath
  split_ifs with h <;> simp [h]

/-- **Heights of a joined path add**: plane height plus tangent height. -/
theorem colH_join (ν : ℕ → ℤ) (κ : ℕ → Fin m → ℤ) (t : ℕ) (c : ℤ) :
    colH (joinPath ν κ t) c = colH (planePath ν t) c + colH (κ t) c := by
  unfold colH
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [joinPath, planePath, Fin.cons_zero, Fin.cons_succ, Finset.univ_unique, Finset.sum_singleton]
  exact congrArg₂ _ (if_congr Iff.rfl rfl rfl) rfl

/-- **Heights are monotone** in the weight. -/
theorem colH_mono {k : ℕ} {μ μ' : Fin k → ℤ} (h : ∀ a, μ a ≤ μ' a) (c : ℤ) : colH μ c ≤ colH μ' c :=
  Finset.card_le_card fun a => by simpa using fun ha : c ≤ μ a => ha.trans (h a)

/-- **A positive height** has a row reaching the column. -/
theorem exists_of_colH_pos {k : ℕ} {μ : Fin k → ℤ} {c : ℤ} (h : 0 < colH μ c) : ∃ a, c ≤ μ a := by
  obtain ⟨a, ha⟩ := Finset.card_pos.1 h
  exact ⟨a, (Finset.mem_filter.1 ha).2⟩

/-- **A plane-dominant joined path** (the PD conditions of C11, column-height form for the tangent strips): `ν` and
`κ` start at `0`; `ν` is nondecreasing and constant across covector letters; vector letters raise `κ` and covector
letters lower it; the tangent rows added by a vector letter sit below the plane row before it (`(C)`); the tangent
height of the column `c` changes by at most one per letter (horizontal strips). -/
structure JoinCond (vec : ℕ → Bool) (ν : ℕ → ℤ) (κ : ℕ → Fin m → ℤ) (c : ℤ) (N : ℕ) : Prop where
  nu0 : ν 0 = 0
  ka0 : κ 0 = 0
  nu_mono : ∀ t < N, ν t ≤ ν (t + 1)
  nu_cov : ∀ t < N, vec t = false → ν (t + 1) = ν t
  ka_vec : ∀ t < N, vec t = true → ∀ b, κ t b ≤ κ (t + 1) b
  ka_cov : ∀ t < N, vec t = false → ∀ b, κ (t + 1) b ≤ κ t b
  ka_le : ∀ t < N, vec t = true → ∀ b, κ (t + 1) b ≤ ν t
  strip : ∀ t < N, colH (κ (t + 1)) c ≤ colH (κ t) c + 1 ∧ colH (κ t) c ≤ colH (κ (t + 1)) c + 1

variable {vec : ℕ → Bool} {ν : ℕ → ℤ} {κ : ℕ → Fin m → ℤ} {c : ℤ} {N : ℕ}

/-- **The joined path is dominant**: `κ_t ≤ ν_t`. -/
theorem JoinCond.dom (hJ : JoinCond vec ν κ c N) {t : ℕ} (ht : t ≤ N) (b : Fin m) : κ t b ≤ ν t := by
  induction t with
  | zero => simp [hJ.nu0, hJ.ka0]
  | succ t ih =>
    cases hv : vec t
    · rw [hJ.nu_cov t (by omega) hv]
      exact (hJ.ka_cov t (by omega) hv b).trans (ih (by omega))
    · exact (hJ.ka_le t (by omega) hv b).trans (hJ.nu_mono t (by omega))

/-- **The tangent height grows only at vector letters.** -/
theorem JoinCond.tgrow (hJ : JoinCond vec ν κ c N) {t : ℕ} (ht : t < N) (h : colH (κ t) c < colH (κ (t + 1)) c) :
    vec t = true := by
  by_contra hv
  have := colH_mono (hJ.ka_cov t ht (by simpa using hv)) c
  omega

/-- **The tangent height drops only at covector letters.** -/
theorem JoinCond.tdrop (hJ : JoinCond vec ν κ c N) {t : ℕ} (ht : t < N) (h : colH (κ (t + 1)) c < colH (κ t) c) :
    vec t = false := by
  by_contra hv
  have := colH_mono (hJ.ka_vec t ht (by simpa using hv)) c
  omega

/-- **The plane row moves only at vector letters.** -/
theorem JoinCond.pgrow (hJ : JoinCond vec ν κ c N) {t : ℕ} (ht : t < N) (h : ν t ≠ ν (t + 1)) : vec t = true := by
  by_contra hv
  exact h (hJ.nu_cov t ht (by simpa using hv)).symm

/-- **The tangent height of a column changes only below the plane row.** -/
theorem JoinCond.sep (hJ : JoinCond vec ν κ c N) {t : ℕ} (ht : t < N) (h : colH (κ t) c ≠ colH (κ (t + 1)) c) :
    c ≤ ν t := by
  rcases lt_or_gt_of_ne h with h | h
  · obtain ⟨b, hb⟩ := exists_of_colH_pos (lt_of_le_of_lt (Nat.zero_le _) h)
    exact hb.trans (hJ.ka_le t ht (hJ.tgrow ht h) b)
  · obtain ⟨b, hb⟩ := exists_of_colH_pos (lt_of_le_of_lt (Nat.zero_le _) h)
    exact hb.trans (hJ.dom ht.le b)

/-- **Before the plane box** (columns `c ≥ 1`) the tangent height is `0`. -/
theorem JoinCond.th_zero (hJ : JoinCond vec ν κ c N) (hc : 1 ≤ c) {t : ℕ} (ht : t ≤ N) (hν : ν t < c) :
    colH (κ t) c = 0 := by
  induction t with
  | zero =>
    rw [hJ.ka0]
    simp [colH]
    omega
  | succ t ih =>
    have h1 : ν t < c := lt_of_le_of_lt (hJ.nu_mono t (by omega)) hν
    have h2 := ih (by omega) h1
    by_contra h3
    exact absurd (hJ.sep (by omega) (by omega)) (not_le.2 h1)

/-- **A plane-dominant joined path satisfies the column conditions.** -/
theorem JoinCond.colCond (hJ : JoinCond vec ν κ c N) : ColCond vec (joinPath ν κ) c N := by
  have hp : ∀ t < N, colH (planePath ν t) c ≤ colH (planePath ν (t + 1)) c := fun t ht => by
    rw [colH_plane, colH_plane]
    have := hJ.nu_mono t ht
    split_ifs <;> omega
  have hp1 : ∀ t, colH (planePath ν t) c ≤ 1 := fun t => by rw [colH_plane]; split_ifs <;> omega
  -- a change of the plane height forces the tangent height to stay
  have hsep : ∀ t < N, colH (planePath ν t) c ≠ colH (planePath ν (t + 1)) c → colH (κ t) c = colH (κ (t + 1)) c :=
    fun t ht h => by
      by_contra h'
      have := hJ.sep ht h'
      rw [colH_plane, colH_plane, ite_eq_left this, ite_eq_left (this.trans (hJ.nu_mono t ht))] at h
      exact h rfl
  have hpv : ∀ t < N, colH (planePath ν t) c < colH (planePath ν (t + 1)) c → vec t = true := fun t ht h => by
    refine hJ.pgrow ht fun he => ?_
    rw [colH_plane, colH_plane, he] at h
    exact lt_irrefl _ h
  refine ⟨fun t ht => ?_, fun t ht h => ?_, fun t ht h => ?_, fun hc => ?_, fun hc t ht => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [colH_join, colH_join]
    have := hJ.strip t ht
    have := hp t ht
    have := hp1 t
    have := hp1 (t + 1)
    by_cases h : colH (planePath ν t) c = colH (planePath ν (t + 1)) c
    · omega
    · have := hsep t ht h
      omega
  · rw [colH_join, colH_join] at h
    by_cases hpe : colH (planePath ν t) c = colH (planePath ν (t + 1)) c
    · exact hJ.tgrow ht (by omega)
    · exact hpv t ht (by have := hp t ht; omega)
  · rw [colH_join, colH_join] at h
    have := hp t ht
    by_cases hpe : colH (planePath ν t) c = colH (planePath ν (t + 1)) c
    · exact hJ.tdrop ht (by omega)
    · have := hsep t ht hpe
      omega
  · rw [colH_join, colH_plane, hJ.nu0, ite_eq_right (by omega), hJ.ka0]
    simp [colH]
    omega
  · have hpl : ∀ u ≤ N, colH (planePath ν u) c = 1 := fun u hu => by
      rw [colH_plane, ite_eq_left ((show c ≤ 0 from hc).trans (hJ.nu0 ▸ mono_of_succ hJ.nu_mono (Nat.zero_le u) hu))]
    rw [colH_join, hpl t ht.le]
    omega
  · have hpl : ∀ u ≤ N, colH (planePath ν u) c = 1 := fun u hu => by
      rw [colH_plane, ite_eq_left ((show c ≤ 0 from hc).trans (hJ.nu0 ▸ mono_of_succ hJ.nu_mono (Nat.zero_le u) hu))]
    rw [colH_join, colH_join, hpl t ht.le, hpl (t + 1) ht] at h
    rw [colH_join, hpl t ht.le]
    omega

end Join

/-! ## The congruence at the identity -/

section Cong

variable {A : Type*} [CommRing A] {m p : ℕ} {π : A}

/-- **The scaled letters**: `ℓ_1` multiplies the scaled variables (`LetterFock.scaled` at type `1`) by `π`. -/
def ysc (π : A) (vec : ℕ → Bool) (x : ℕ → Fin (m + 1) → A) (t : ℕ) (a : Fin (m + 1)) : A :=
  (if scaled 1 vec (t, a) then π else 1) * x t a

/-- **A scaled vector letter** at the plane coordinate. -/
theorem ysc_vec0 {vec : ℕ → Bool} {x : ℕ → Fin (m + 1) → A} {t : ℕ} (ht : vec t = true) :
    ysc π vec x t 0 = x t 0 := by
  simp [ysc, scaled, ht]

/-- **A scaled vector letter** at a tangent coordinate. -/
theorem ysc_vecs {vec : ℕ → Bool} {x : ℕ → Fin (m + 1) → A} {t : ℕ} (ht : vec t = true) (b : Fin m) :
    ysc π vec x t b.succ = π * x t b.succ := by
  simp [ysc, scaled, ht]

/-- **A scaled covector letter** at the plane coordinate. -/
theorem ysc_cov0 {vec : ℕ → Bool} {x : ℕ → Fin (m + 1) → A} {t : ℕ} (ht : vec t = false) :
    ysc π vec x t 0 = π * x t 0 := by
  simp [ysc, scaled, ht]

/-- **A scaled covector letter** at a tangent coordinate. -/
theorem ysc_covs {vec : ℕ → Bool} {x : ℕ → Fin (m + 1) → A} {t : ℕ} (ht : vec t = false) (b : Fin m) :
    ysc π vec x t b.succ = x t b.succ := by
  simp [ysc, scaled, ht]

/-- **`[∅]` splits** into the plane and tangent parts. -/
theorem st0_split (J : Finset (Fin (m + 1))) : (st0 J : A) = st0 (pl0 J) * st0 (tanPart J) := by
  unfold st0 pl0
  by_cases h : J = ∅
  · subst h
    simp [tanPart]
  · rw [ite_eq_right h]
    rw [eq_empty_iff_split, not_and_or, not_not] at h
    rcases h with h | h
    · simp [h]
    · simp [h]

variable {k : ℕ}

/-- **Freshness at stage `t`**: every height-changing letter before `t` has a smaller position. -/
def fresh (μ : ℕ → Fin k → ℤ) (pos : ℕ → ℕ) (c : ℤ) (t : ℕ) : Prop :=
  ∀ i < t, colH (μ i) c ≠ colH (μ (i + 1)) c → pos i < pos t

/-- **Strictness** (T9f): if `i < t`, the letter `i` changes the height and `t` is costly, then `pos i < pos t`. -/
def Strict (pos : ℕ → ℕ) (μ : ℕ → Fin k → ℤ) (c : ℤ) (N : ℕ) : Prop :=
  ∀ i t, i < t → t < N → colH (μ i) c ≠ colH (μ (i + 1)) c → costly μ c t → pos i < pos t

/-- **A strict position step** gives a Frobenius exponent `≥ 2`. -/
theorem two_le_frobExp (hp : p.Prime) {pos : ℕ → ℕ} {t : ℕ} (h : pos t < pos (t + 1)) : 2 ≤ frobExp p pos t :=
  hp.two_le.trans (by
    unfold frobExp
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (pos (t + 1) - pos t) := Nat.pow_le_pow_right hp.pos (by omega))

/-- **Freshness after a height change** needs a strict position step. -/
theorem fresh_succ_change (hp : p.Prime) {μ : ℕ → Fin k → ℤ} {pos : ℕ → ℕ} {c : ℤ} {t : ℕ}
    (h : colH (μ t) c ≠ colH (μ (t + 1)) c) (hf : fresh μ pos c (t + 1)) : 2 ≤ frobExp p pos t :=
  two_le_frobExp hp (hf t (Nat.lt_succ_self t) h)

/-- **Freshness after a keep step**: fresh before, or a strict position step. -/
theorem fresh_succ_keep (hp : p.Prime) {μ : ℕ → Fin k → ℤ} {pos : ℕ → ℕ} {c : ℤ} {t : ℕ}
    (hpos : pos t ≤ pos (t + 1)) (hf : fresh μ pos c (t + 1)) : fresh μ pos c t ∨ 2 ≤ frobExp p pos t := by
  by_cases hlt : pos t < pos (t + 1)
  · exact Or.inr (two_le_frobExp hp hlt)
  · exact Or.inl fun i hi hc => by have := hf i (by omega) hc; omega

/-- **The congruence of the lifted twisted column state at the identity** (the core of T9f(cong)), over any
commutative ring: for a plane-dominant joined path with strictness, the twisted state of the scaled letters is
`π^{cost}` times the product of the twisted plane and tangent states, modulo `π^{cost + 1}`. -/
theorem cong_core (hp : p.Prime) {vec : ℕ → Bool} {x : ℕ → Fin (m + 1) → A} {pos : ℕ → ℕ} {ν : ℕ → ℤ}
    {κ : ℕ → Fin m → ℤ} {c : ℤ} {N : ℕ} (hpos : ∀ t < N, pos t ≤ pos (t + 1)) (hJ : JoinCond vec ν κ c N)
    (hst : Strict pos (joinPath ν κ) c N) (J : Finset (Fin (m + 1))) :
    π ^ (cost p pos (joinPath ν κ) c N + 1) ∣
      colSt (ysc π vec x) (colStep (joinPath ν κ) c) (frobExp p pos) N J -
      π ^ cost p pos (joinPath ν κ) c N *
        (colSt (fun t _ => x t 0) (colStep (planePath ν) c) (frobExp p pos) N (pl0 J) *
          colSt (fun t b => x t b.succ) (colStep κ c) (frobExp p pos) N (tanPart J)) := by
  have hq : ∀ t, 1 ≤ frobExp p pos t := fun t => Nat.one_le_pow _ _ hp.pos
  have hp1 : ∀ t, colH (planePath ν t) c ≤ 1 := fun t => by rw [colH_plane]; split_ifs <;> omega
  have hpm : ∀ t < N, colH (planePath ν t) c ≤ colH (planePath ν (t + 1)) c := fun t ht => by
    rw [colH_plane, colH_plane]
    have := hJ.nu_mono t ht
    split_ifs <;> omega
  have hsep : ∀ t < N, colH (κ t) c ≠ colH (κ (t + 1)) c → colH (planePath ν t) c = 1 := fun t ht h => by
    rw [colH_plane, ite_eq_left (hJ.sep ht h)]
  have hfr : ∀ t < N, costly (joinPath ν κ) c t → fresh (joinPath ν κ) pos c t :=
    fun t ht hco i hi hc => hst i t hi ht hc hco
  have hc0 : (cost p pos (joinPath ν κ) c 0) = 0 := by simp [cost]
  by_cases hc : 1 ≤ c
  · have key : ∀ t ≤ N, InvL π (cost p pos (joinPath ν κ) c t) (colH (planePath ν t) c = 1)
        (fresh (joinPath ν κ) pos c t) (colSt (ysc π vec x) (colStep (joinPath ν κ) c) (frobExp p pos) t)
        (colSt (fun t _ => x t 0) (colStep (planePath ν) c) (frobExp p pos) t)
        (colSt (fun t b => x t b.succ) (colStep κ c) (frobExp p pos) t) := by
      intro t ht
      induction t with
      | zero =>
        have hp0 : colH (planePath ν 0) c = 0 := by rw [colH_plane, hJ.nu0, ite_eq_right (by omega)]
        refine ⟨fun h => by omega, fun J => ?_, fun J _ hJ' => ?_, fun _ J _ hJ' => ?_⟩
        · rw [hc0, pow_zero, one_mul]
          simp only [colSt]
          rw [← st0_split, sub_self]
          exact dvd_zero _
        · simp [colSt, st0, hJ'.resolve_right (by omega)]
        · simp [colSt, st0, hJ'.resolve_right (by omega)]
      | succ t ih =>
        have htN : t < N := by omega
        have I := ih (by omega)
        rw [colSt_succ, colSt_succ, colSt_succ, cost_succ hpos _ c htN]
        have hjt := colH_join ν κ t c
        have hjt1 := colH_join ν κ (t + 1) c
        have hs := hJ.strip t htN
        have hpm' := hpm t htN
        have hp1t := hp1 t
        have hp1t1 := hp1 (t + 1)
        by_cases hpc : colH (planePath ν t) c < colH (planePath ν (t + 1)) c
        · -- the plane box
          have hth : colH (κ t) c = colH (κ (t + 1)) c := by
            by_contra h
            have := hsep t htN h
            omega
          have hνt : ν t < c := by
            by_contra h
            rw [colH_plane, ite_eq_left (not_lt.1 h)] at hpc
            omega
          have hth0 := hJ.th_zero hc htN.le hνt
          have hvec := hJ.pgrow htN fun he => by rw [colH_plane, colH_plane, he] at hpc; exact lt_irrefl _ hpc
          have hco : ¬costly (joinPath ν κ) c t := by unfold costly; omega
          rw [colStep_grow (show colH (joinPath ν κ t) c < colH (joinPath ν κ (t + 1)) c by omega),
            colStep_grow hpc, colStep_keep hth, ite_eq_left hc]
          simp only [Step.app]
          have I0 := I.mono rfl (show False ↔ colH (planePath ν t) c = 1 from ⟨False.elim, fun h => by omega⟩) id
          refine ((I0.plane (ysc_vec0 hvec) (ysc_vecs hvec)).pow (hq t)).mono ?_ ?_ ?_
          · rw [ite_eq_right hco, add_zero]
            rfl
          · exact ⟨fun _ => trivial, fun _ => by omega⟩
          · exact fun hf => Or.inr (fresh_succ_change hp (by omega) hf)
        · have hpe : colH (planePath ν t) c = colH (planePath ν (t + 1)) c := by omega
          by_cases hk : colH (κ t) c < colH (κ (t + 1)) c
          · -- a tangent box from a vector letter
            have hpt := hsep t htN (by omega)
            have hvec := hJ.tgrow htN hk
            have hco : costly (joinPath ν κ) c t := by unfold costly; omega
            rw [colStep_grow (show colH (joinPath ν κ t) c < colH (joinPath ν κ (t + 1)) c by omega),
              colStep_keep hpe, colStep_grow hk, ite_eq_left hc]
            simp only [Step.app]
            have I1 := I.mono (fr' := True) rfl
              (show True ↔ colH (planePath ν t) c = 1 from ⟨fun _ => hpt, fun _ => trivial⟩) fun _ => hfr t htN hco
            refine ((I1.tgrow (ysc_vec0 hvec) (ysc_vecs hvec)).pow (hq t)).mono ?_ ?_ ?_
            · rw [ite_eq_left hco]
              rfl
            · exact ⟨fun _ => trivial, fun _ => by omega⟩
            · exact fun hf => Or.inr (fresh_succ_change hp (by omega) hf)
          · by_cases hk' : colH (κ (t + 1)) c < colH (κ t) c
            · -- a tangent box removed by a covector letter
              have hpt := hsep t htN (by omega)
              have hvec := hJ.tdrop htN hk'
              have hco : ¬costly (joinPath ν κ) c t := by unfold costly; omega
              rw [colStep_drop (show colH (joinPath ν κ (t + 1)) c < colH (joinPath ν κ t) c by omega),
                colStep_keep hpe, colStep_drop hk', ite_eq_left hc]
              simp only [Step.app]
              have I1 := I.mono rfl (show True ↔ colH (planePath ν t) c = 1 from ⟨fun _ => hpt, fun _ => trivial⟩) id
              refine ((I1.tdrop (ysc_cov0 hvec) (ysc_covs hvec)).pow (hq t)).mono ?_ ?_ ?_
              · rw [ite_eq_right hco, add_zero]
                rfl
              · exact ⟨fun _ => trivial, fun _ => by omega⟩
              · exact fun hf => Or.inr (fresh_succ_change hp (by omega) hf)
            · -- nothing changes
              have hth : colH (κ t) c = colH (κ (t + 1)) c := by omega
              have hco : ¬costly (joinPath ν κ) c t := by unfold costly; omega
              rw [colStep_keep (show colH (joinPath ν κ t) c = colH (joinPath ν κ (t + 1)) c by omega),
                colStep_keep hpe, colStep_keep hth]
              simp only [Step.app]
              refine (I.pow (hq t)).mono ?_ ?_ ?_
              · rw [ite_eq_right hco, add_zero]
                rfl
              · rw [hpe]
              · exact fresh_succ_keep hp (hpos t htN)
    exact (key N le_rfl).lead J
  · have hc' : c ≤ 0 := by omega
    have hpl : ∀ t ≤ N, colH (planePath ν t) c = 1 := fun t ht => by
      rw [colH_plane, ite_eq_left (hc'.trans (hJ.nu0 ▸ mono_of_succ hJ.nu_mono (Nat.zero_le t) ht))]
    have hPl : ∀ t ≤ N, colSt (fun t (_ : Fin 1) => x t 0) (colStep (planePath ν) c) (frobExp p pos) t = st0 := by
      intro t ht
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [colSt_succ, colStep_keep (by rw [hpl t (by omega), hpl (t + 1) ht]), ih (by omega)]
        exact funext fun J => st0_pow J (by have := hq t; omega)
    have key : ∀ t ≤ N, InvD π (cost p pos (joinPath ν κ) c t) (fresh (joinPath ν κ) pos c t)
        (colSt (ysc π vec x) (colStep (joinPath ν κ) c) (frobExp p pos) t)
        (colSt (fun t b => x t b.succ) (colStep κ c) (frobExp p pos) t) := by
      intro t ht
      induction t with
      | zero =>
        refine ⟨fun J => ?_, fun J h0 => ?_, fun _ J h0 => ?_⟩
        · rw [hc0, pow_zero, one_mul]
          simp only [colSt]
          rw [← st0_split, sub_self]
          exact dvd_zero _
        · simp [colSt, st0, Finset.ne_empty_of_mem h0]
        · simp [colSt, st0, Finset.ne_empty_of_mem h0]
      | succ t ih =>
        have htN : t < N := by omega
        have I := ih (by omega)
        rw [colSt_succ, colSt_succ, cost_succ hpos _ c htN]
        have hjt := colH_join ν κ t c
        have hjt1 := colH_join ν κ (t + 1) c
        have hpt := hpl t htN.le
        have hpt1 := hpl (t + 1) ht
        by_cases hk : colH (κ t) c < colH (κ (t + 1)) c
        · have hvec := hJ.tgrow htN hk
          have hco : costly (joinPath ν κ) c t := by unfold costly; omega
          rw [colStep_grow (show colH (joinPath ν κ t) c < colH (joinPath ν κ (t + 1)) c by omega),
            colStep_grow hk, ite_eq_right hc]
          simp only [Step.app]
          have I1 := (I.mono (fr' := True) rfl fun _ => hfr t htN hco).tgrow (ysc_vec0 (π := π) (x := x) hvec)
            (ysc_vecs (π := π) (x := x) hvec)
          refine (I1.pow (hq t)).mono ?_ fun hf => Or.inr (fresh_succ_change hp (by omega) hf)
          rw [ite_eq_left hco]
          rfl
        · by_cases hk' : colH (κ (t + 1)) c < colH (κ t) c
          · have hvec := hJ.tdrop htN hk'
            have hco : ¬costly (joinPath ν κ) c t := by unfold costly; omega
            rw [colStep_drop (show colH (joinPath ν κ (t + 1)) c < colH (joinPath ν κ t) c by omega),
              colStep_drop hk', ite_eq_right hc]
            simp only [Step.app]
            refine ((I.tdrop (ysc_cov0 hvec) (ysc_covs hvec)).pow (hq t)).mono ?_
              fun hf => Or.inr (fresh_succ_change hp (by omega) hf)
            rw [ite_eq_right hco, add_zero]
            rfl
          · have hth : colH (κ t) c = colH (κ (t + 1)) c := by omega
            have hco : ¬costly (joinPath ν κ) c t := by unfold costly; omega
            rw [colStep_keep (show colH (joinPath ν κ t) c = colH (joinPath ν κ (t + 1)) c by omega),
              colStep_keep hth]
            simp only [Step.app]
            refine (I.pow (hq t)).mono ?_ (fresh_succ_keep hp (hpos t htN))
            rw [ite_eq_right hco, add_zero]
            rfl
    rw [hPl N le_rfl]
    exact (key N le_rfl).lead J

end Cong

/-! ## T9f(cong): the leading term at the identity over `Kf` -/

section CongLift

variable {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] {ι : Qq →+* Kf}
  {σ : Qq ≃+* Qq} {j : W →+* O} {ϖ : O} {p n' m : ℕ}

variable (Kf) in
/-- **The Frobenius map** `Frob_z : X_{t,b} ↦ X_{t,b}^{p^{z − pos t}}`, `z = pos N`. -/
def frobZ {k : ℕ} (p : ℕ) (pos : ℕ → ℕ) (N : ℕ) : MvPolynomial (ℕ × Fin k) Kf →ₐ[Kf] MvPolynomial (ℕ × Fin k) Kf :=
  aeval fun v => X v ^ p ^ (pos N - pos v.1)

variable (Kf) in
/-- **`planeTan_c(J)`**: the untwisted column state of the plane path at `J ∩ {0}` times that of the tangent path at
`J ∖ {0}`, in the joined coordinates (the plane coordinate is `0`, the tangent coordinate `b` is `b + 1`). -/
def planeTan (ν : ℕ → ℤ) (κ : ℕ → Fin m → ℤ) (c : ℤ) (N : ℕ) (J : Finset (Fin (m + 1))) :
    MvPolynomial (ℕ × Fin (m + 1)) Kf :=
  rename (fun v : ℕ × Fin 1 => (v.1, (0 : Fin (m + 1)))) (colK Kf (planePath ν) c N (pl0 J)) *
    rename (fun v : ℕ × Fin m => (v.1, v.2.succ)) (colK Kf κ c N (tanPart J))

/-- **The plane column state with a plane box** (columns `c ≥ 1`): if the letter `t₀ < N` adds the box of the column
`c` to the nondecreasing plane row (`ν t₀ < c ≤ ν (t₀ + 1)`), the plane state is `X_{t₀,0}` at `{0}` and `0` at `∅`
(so `Frob_z` of it is the plane monomial `X_{t₀,0}^{p^{z − pos t₀}}`). -/
theorem colK_plane {ν : ℕ → ℤ} {c : ℤ} {N t0 : ℕ} (hc : 1 ≤ c) (hmono : ∀ t < N, ν t ≤ ν (t + 1)) (ht0 : t0 < N)
    (hlt : ν t0 < c) (hle : c ≤ ν (t0 + 1)) :
    colK Kf (planePath ν) c N univ = X (t0, 0) ∧ colK Kf (planePath ν) c N ∅ = 0 := by
  have e1 : ∀ S : Finset (Fin 1) → MvPolynomial (ℕ × Fin 1) Kf, pw 1 S = S := fun S => funext fun J => pow_one _
  have hbefore : ∀ t ≤ t0, colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin 1) Kf)) (colStep (planePath ν) c)
      (fun _ => 1) t = st0 := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      have h1 : ν (t + 1) < c := lt_of_le_of_lt (mono_of_succ hmono ht (by omega)) hlt
      have h2 : ν t < c := lt_of_le_of_lt (hmono t (by omega)) h1
      rw [colSt_succ, colStep_keep (by rw [colH_plane, colH_plane, ite_eq_right (not_le.2 h1),
        ite_eq_right (not_le.2 h2)]), ih (by omega), e1]
      rfl
  have hafter : ∀ t, t0 + 1 ≤ t → t ≤ N → colSt (fun t a => (X (t, a) : MvPolynomial (ℕ × Fin 1) Kf))
      (colStep (planePath ν) c) (fun _ => 1) t = wedge (fun a => X (t0, a)) st0 := by
    intro t ht htN
    induction t, ht using Nat.le_induction with
    | base =>
      have hg : colH (planePath ν t0) c < colH (planePath ν (t0 + 1)) c := by
        rw [colH_plane, colH_plane, ite_eq_right (not_le.2 hlt), ite_eq_left hle]
        omega
      rw [colSt_succ, colStep_grow hg, ite_eq_left hc, hbefore t0 le_rfl, e1]
      rfl
    | succ t ht' ih =>
      have h1 : c ≤ ν t := hle.trans (mono_of_succ hmono ht' (by omega))
      rw [colSt_succ, colStep_keep (by rw [colH_plane, colH_plane, ite_eq_left h1,
        ite_eq_left (h1.trans (hmono t (by omega)))]), ih (by omega), e1]
      rfl
  have h := hafter N (by omega) le_rfl
  rw [colK, h, wedge_one_univ]
  exact ⟨by simp [st0], by simp [wedge]⟩

/-- **The plane column state without a plane box**: if the plane height of the column `c` never changes (`c ≤ 0`, or
`c` beyond the final plane row), the plane state is `[∅]`. -/
theorem colK_plane_const {ν : ℕ → ℤ} {c : ℤ} {N : ℕ} (h : ∀ t < N, (c ≤ ν t ↔ c ≤ ν (t + 1))) :
    colK Kf (planePath ν) c N = st0 := by
  unfold colK
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [colSt_succ, colStep_keep (by rw [colH_plane, colH_plane]; exact if_congr (h N (by omega)) rfl rfl),
      ih fun t ht => h t (by omega)]
    exact funext fun J => pow_one _

/-- **(cong)** At `g = 1`, for a plane-dominant joined path with strictness, the lift of the twisted column state is
`ϖ^{cost(c)}·Frob_z(planeTan_c(J))` modulo `ϖ^{cost(c) + 1}`. -/
theorem twCol_cong (hU : Unram p n' W Qq O Kf ι σ j ϖ) {vec : ℕ → Bool} {pos : ℕ → ℕ} {ν : ℕ → ℤ}
    {κ : ℕ → Fin m → ℤ} {c : ℤ} {N : ℕ} (hpos : ∀ t < N, pos t ≤ pos (t + 1)) (hJ : JoinCond vec ν κ c N)
    (hst : Strict pos (joinPath ν κ) c N) (J : Finset (Fin (m + 1))) :
    OrdGe ϖ (cost p pos (joinPath ν κ) c N + 1)
      (liftSub ι σ ϖ 1 vec pos (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) W) (twCol Kf p pos (joinPath ν κ) c N J) -
        C (algebraMap O Kf ϖ ^ cost p pos (joinPath ν κ) c N) * frobZ Kf p pos N (planeTan Kf ν κ c N J)) := by
  set n := cost p pos (joinPath ν κ) c N
  let x : ℕ → Fin (m + 1) → MvPolynomial (ℕ × Fin (m + 1)) O := fun t a => X (t, a)
  have hπ : C ϖ ∣ (p : MvPolynomial (ℕ × Fin (m + 1)) O) :=
    ⟨C ϖ, by rw [← map_natCast C, ← hU.sq, map_pow, sq]⟩
  -- the lift at the identity is the image of the scaled letters
  have e1 : liftSub ι σ ϖ 1 vec pos (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) W) (twCol Kf p pos (joinPath ν κ) c N J) =
      map (algebraMap O Kf) (colSt (ysc (C ϖ) vec x) (colStep (joinPath ν κ) c) (frobExp p pos) N J) := by
    rw [twCol, ← AlgHom.coe_toRingHom, map_colSt, map_colSt]
    congr 1
    funext t a
    simp only [AlgHom.coe_toRingHom, liftSub_one_X, ysc, x, map_mul, map_X, apply_ite, map_C, map_one]
  -- the Frobenius image of `planeTan` is the image of the untwisted states of the raised letters
  have e2 : frobZ Kf p pos N (planeTan Kf ν κ c N J) = map (algebraMap O Kf)
      (colSt (fun u (_ : Fin 1) => x u 0 ^ p ^ (pos N - pos u)) (colStep (planePath ν) c) (fun _ => 1) N (pl0 J) *
        colSt (fun u b => x u b.succ ^ p ^ (pos N - pos u)) (colStep κ c) (fun _ => 1) N (tanPart J)) := by
    rw [planeTan, map_mul, map_mul, colK, colK, ← AlgHom.coe_toRingHom, ← AlgHom.coe_toRingHom (rename _),
      map_colSt, map_colSt, ← AlgHom.coe_toRingHom (rename _), map_colSt, map_colSt, map_colSt, map_colSt]
    congr 2 <;> funext u a <;> simp [frobZ, x]
  rw [e1, e2, show C ((algebraMap O Kf) ϖ ^ n) = map (algebraMap O Kf) (C ϖ ^ n) by
    rw [map_pow, map_pow, map_C], ← map_mul, ← map_sub]
  refine ordGe_map ?_
  have h1 := cong_core (π := C ϖ) (x := x) hU.prime hpos hJ hst J
  have h2 := tw_frob hU.prime (fun u (_ : Fin 1) => x u 0) (colStep (planePath ν) c) hpos le_rfl (pl0 J)
  have h3 := tw_frob hU.prime (fun u b => x u b.succ) (colStep κ c) hpos le_rfl (tanPart J)
  set T := colSt (ysc (C ϖ) vec x) (colStep (joinPath ν κ) c) (frobExp p pos) N J
  set P := colSt (fun u (_ : Fin 1) => x u 0) (colStep (planePath ν) c) (frobExp p pos) N (pl0 J)
  set Q := colSt (fun u b => x u b.succ) (colStep κ c) (frobExp p pos) N (tanPart J)
  set P' := colSt (fun u (_ : Fin 1) => x u 0 ^ p ^ (pos N - pos u)) (colStep (planePath ν) c) (fun _ => 1) N (pl0 J)
  set Q' := colSt (fun u b => x u b.succ ^ p ^ (pos N - pos u)) (colStep κ c) (fun _ => 1) N (tanPart J)
  have h4 : C ϖ ^ (n + 1) ∣ C ϖ ^ n * (P * Q - P' * Q') := by
    rw [pow_succ]
    refine mul_dvd_mul_left _ (hπ.trans ?_)
    rw [show P * Q - P' * Q' = P * (Q - Q') + (P - P') * Q' by ring]
    exact dvd_add (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_right h2 _)
  rw [show T - C ϖ ^ n * (P' * Q') = (T - C ϖ ^ n * (P * Q)) + C ϖ ^ n * (P * Q - P' * Q') by ring]
  exact dvd_add h1 h4

end CongLift

end

end TwistedDegree
