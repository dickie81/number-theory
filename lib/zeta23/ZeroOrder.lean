import CountCompare
import RiemannKernel

/-! # The order of a zero of `ζ` is `O(log |γ|)`, with explicit constants

`CountCompare.local_count_le` bounds the nontrivial zeros of `ζ` with `t < Im ρ ≤ t + 1`, `t ≥ 0`, counted with
multiplicity, by `Kloc (t + ½) = (13/2)(5 + κ + ½ log(t + 5/2))`, where `κ = Σ_n Λ(n)n^{−3/2}` (`Kaiser.kLam`,
which is `−ζ′(3/2)/ζ(3/2) ≈ 1.505`). A zero at height `γ > 0` lies in the window with `t = max(0, γ − ½)`, so its
order is at most `Kloc (γ + ½)`. Conjugation preserves the order (`Zeta23.analyticOrderAt_zeta_conj`), which gives
`γ < 0`, and `ξ(σ) ≠ 0` for real `σ` (`WeilForm.xi_real_ne_zero`) rules out `γ = 0`.

* `im_ne_zero`: no nontrivial zero of `ζ` is real.
* `zeroMult_le_of_im_pos`: the order of a zero with `Im ρ > 0` is at most `Kloc (Im ρ + ½)`.
* `analyticOrderAt_le`: every nontrivial zero `ρ` of `ζ` has order at most `⌊Kloc (|Im ρ| + ½)⌋`, about
  `(13/4)log(|Im ρ| + 5/2) + 42.3`.
-/

open Complex ComplexConjugate

namespace ZeroOrder

open ShortWeil

/-- **No nontrivial zero of `ζ` is real**: `ξ(σ) ≠ 0` for every real `σ`. -/
theorem im_ne_zero {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) : ρ.im ≠ 0 := by
  intro h
  have hx := WeilForm.xi_eq_zero_of_nontrivial ((CountCompare.nontriv_iff' ρ).2 hρ)
  have e : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [h])
  rw [e] at hx
  exact WeilForm.xi_real_ne_zero ρ.re hx

/-- **The order of a zero in the upper half-plane**: a nontrivial zero `ρ` of `ζ` with `Im ρ > 0` has order at most
`Kloc (Im ρ + ½)`, since the window `max(0, Im ρ − ½) < Im s ≤ max(0, Im ρ − ½) + 1` holds it. -/
theorem zeroMult_le_of_im_pos {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) (hγ : 0 < ρ.im) :
    (Zeta23.zeroMult ρ : ℝ) ≤ Kloc (ρ.im + 1 / 2) := by
  classical
  set t : ℝ := max 0 (ρ.im - 1 / 2) with ht
  have ht0 : 0 ≤ t := le_max_left _ _
  have ht1 : t < ρ.im := max_lt hγ (by linarith)
  have ht2 : ρ.im ≤ t + 1 := by
    have := le_max_right 0 (ρ.im - 1 / 2)
    linarith
  have ht3 : t ≤ ρ.im := max_le hγ.le (by linarith)
  have hfin : (Zeta23.zerosIn t (t + 1)).Finite :=
    (SlogZeta.Zs_finite (t + 2)).subset fun z ⟨hz, hz0, hz1⟩ => ⟨hz, by linarith, by linarith⟩
  have hmem : ρ ∈ Zeta23.zerosIn t (t + 1) := ⟨hρ, ht1, ht2⟩
  have hle : Zeta23.zeroMult ρ ≤ Zeta23.Ncount t (t + 1) := by
    rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.2 hmem)
  calc (Zeta23.zeroMult ρ : ℝ) ≤ Zeta23.Ncount t (t + 1) := by exact_mod_cast hle
    _ ≤ Kloc (t + 1 / 2) := CountCompare.local_count_le ht0
    _ ≤ Kloc (ρ.im + 1 / 2) := Kloc_mono (by linarith) (by linarith)

/-- **The order of a zero of `ζ` is `O(log |γ|)`**: every nontrivial zero `ρ` of `ζ` has order at most
`⌊Kloc (|Im ρ| + ½)⌋`, where `Kloc x = (13/2)(5 + κ + ½ log(x + 2))` and `κ = Σ_n Λ(n)n^{−3/2}`. -/
theorem analyticOrderAt_le {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤ ⌊Kloc (|ρ.im| + 1 / 2)⌋₊ := by
  have hnt : Zeta23.IsNontrivialZero ρ := ⟨hρ, h0, h1⟩
  have hne1 : ρ ≠ 1 := by
    rintro rfl
    norm_num at h1
  have hpos := WeilTest.zeroMult_pos ⟨ρ, (CountCompare.nontriv_iff' ρ).2 hnt⟩
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h
    simp [WeilTest.zeroMult, h] at hpos
  have key : (Zeta23.zeroMult ρ : ℝ) ≤ Kloc (|ρ.im| + 1 / 2) := by
    rcases lt_trichotomy ρ.im 0 with hlt | heq | hgt
    · have hc : Zeta23.IsNontrivialZero (conj ρ) :=
        ⟨by rw [riemannZeta_conj, hρ, map_zero], by simpa using h0, by simpa using h1⟩
      have hm : Zeta23.zeroMult (conj ρ) = Zeta23.zeroMult ρ := by
        unfold Zeta23.zeroMult
        rw [Zeta23.analyticOrderAt_zeta_conj hne1]
      have h' := zeroMult_le_of_im_pos hc (by simpa using hlt)
      rw [hm, Complex.conj_im] at h'
      rwa [abs_of_neg hlt]
    · exact absurd heq (im_ne_zero hnt)
    · rw [abs_of_pos hgt]
      exact zeroMult_le_of_im_pos hnt hgt
  have hn : Zeta23.zeroMult ρ ≤ ⌊Kloc (|ρ.im| + 1 / 2)⌋₊ := Nat.le_floor key
  calc analyticOrderAt riemannZeta ρ = ((analyticOrderAt riemannZeta ρ).toNat : ℕ∞) :=
        (ENat.natCast_toNat htop).symm
    _ ≤ _ := by exact_mod_cast hn

end ZeroOrder

#print axioms ZeroOrder.im_ne_zero
#print axioms ZeroOrder.zeroMult_le_of_im_pos
#print axioms ZeroOrder.analyticOrderAt_le
