import ShortSieveMoment
import ShortSieveTwist

/-!
# Harman's moment lemma for the primes

For the Dirichlet polynomial of the primes of `(N, 2N]`, `P(t) = Σ_{N<p≤2N} p^{−it}` (`DirMean.dp` of the primes with
coefficient `1`), the twisted prime number theorem gives `|P(t)| ≤ C N^{99/100}` for `N^{1/100} ≤ |t| ≤ N^A`
(`ShortSieveTwist.norm_dp_primes_Ioc_le`). That is the pointwise bound `|P| ≤ N^{1−1/200}` (for `N` large) that the
moment lemmas of `ShortSieveMoment` take, so on heights `N^{1/100} ≤ a ≤ b ≤ N^D`, with no hypothesis:

* `moment_primes_hux`: for `m < D ≤ m + 1/2` and `δ > 4D − 2m`, `∫_a^b |P|^δ ≤ C N^{δ−η}` for some `η > 0`;
* `moment_primes_mv`: the same for `D ≤ k` and `δ > 2k`.

Their only analytic input beyond the large values estimates is the zero-free half-plane `Re s > 11/12`.
-/

open Finset Real DirMean

namespace ShortSieveHarman

/-- The pointwise bound on the heights `[N^{1/100}, N^D]`, in the form of `ShortSieveMoment`'s hypothesis with
`η₁ = 1/200`. -/
lemma pointwise {Dx : ℝ} (hDx : 0 < Dx) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ t →
    t ≤ (N : ℝ) ^ Dx →
      ‖dp ((Ioc N (2 * N)).filter Nat.Prime) (fun _ => 1) t‖ ≤ (N : ℝ) ^ (1 - 1 / 200 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := ShortSieveTwist.norm_dp_primes_Ioc_le hDx
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → C ≤ (N : ℝ) ^ (1 / 200 : ℝ) := by
    refine ⟨⌈C ^ (200 : ℝ)⌉₊, fun N hN => ?_⟩
    have hN' : C ^ (200 : ℝ) ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    calc C = (C ^ (200 : ℝ)) ^ (1 / 200 : ℝ) := by rw [← Real.rpow_mul hC0]; norm_num
      _ ≤ (N : ℝ) ^ (1 / 200 : ℝ) := Real.rpow_le_rpow (by positivity) hN' (by norm_num)
  refine ⟨max N₁ 2, fun N hN t ht1 ht2 => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by positivity
  have ht0 : 0 ≤ t := le_trans (by positivity) ht1
  have h := hC N hN2 (2 * N) (by omega) le_rfl t (by rwa [abs_of_nonneg ht0]) (by rwa [abs_of_nonneg ht0])
  calc ‖dp ((Ioc N (2 * N)).filter Nat.Prime) (fun _ => 1) t‖ ≤ C * (N : ℝ) ^ (99 / 100 : ℝ) := h
    _ ≤ (N : ℝ) ^ (1 / 200 : ℝ) * (N : ℝ) ^ (99 / 100 : ℝ) := by
        gcongr
        exact hN₁ N (le_trans (le_max_left _ _) hN)
    _ = (N : ℝ) ^ (1 - 1 / 200 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num

/-- **Harman's moment lemma for the primes, with real exponents.** For `m ≥ 1`, `m < D ≤ m + 1/2` and
`δ > 4D − 2m` there are `η > 0`, `C` and `N₀` with `∫_a^b |Σ_{N<p≤2N} p^{−it}|^δ dt ≤ C N^{δ−η}` for every `N ≥ N₀`
and `N^{1/100} ≤ a ≤ b ≤ N^D`. -/
theorem moment_primes_hux {m : ℕ} (hm : 1 ≤ m) {Dx δ : ℝ} (hD : (m : ℝ) < Dx) (hD' : Dx ≤ m + 1 / 2)
    (hδ : 4 * Dx - 2 * m < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a b : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ a → a ≤ b →
      b ≤ (N : ℝ) ^ Dx →
        ∫ t in a..b, ‖dp ((Ioc N (2 * N)).filter Nat.Prime) (fun _ => 1) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) := by
  have hDx : 0 < Dx := lt_of_le_of_lt (Nat.cast_nonneg m) hD
  obtain ⟨η, hη, C, N₀, hmom⟩ := ShortSieveMoment.moment_le_hux hm hD hD' hδ (η₁ := 1 / 200) (by norm_num)
  obtain ⟨N₁, hpt⟩ := pointwise hDx
  refine ⟨η, hη, C, max N₀ N₁, fun N hN a b ha hab hb => ?_⟩
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  exact hmom N (le_trans (le_max_left _ _) hN) _ (filter_subset _ _) _ (fun _ _ => by simp) a b hab
    (by linarith) fun t ht => hpt N (le_trans (le_max_right _ _) hN) t (le_trans ha ht.1) (le_trans ht.2 hb)

/-- **Harman's moment lemma for the primes from the mean value theorem.** For `k ≥ 1`, `D ≤ k` and `δ > 2k` there are
`η > 0`, `C` and `N₀` with `∫_a^b |Σ_{N<p≤2N} p^{−it}|^δ dt ≤ C N^{δ−η}` for every `N ≥ N₀` and
`N^{1/100} ≤ a ≤ b ≤ N^D`, `D > 0`. -/
theorem moment_primes_mv {k : ℕ} (hk : 1 ≤ k) {Dx δ : ℝ} (hDx : 0 < Dx) (hD : Dx ≤ k) (hδ : 2 * k < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a b : ℝ, (N : ℝ) ^ (1 / 100 : ℝ) ≤ a → a ≤ b →
      b ≤ (N : ℝ) ^ Dx →
        ∫ t in a..b, ‖dp ((Ioc N (2 * N)).filter Nat.Prime) (fun _ => 1) t‖ ^ δ ≤ C * (N : ℝ) ^ (δ - η) := by
  obtain ⟨η, hη, C, N₀, hmom⟩ := ShortSieveMoment.moment_le_mv hk hD hδ (η₁ := 1 / 200) (by norm_num)
  obtain ⟨N₁, hpt⟩ := pointwise hDx
  refine ⟨η, hη, C, max N₀ N₁, fun N hN a b ha hab hb => ?_⟩
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  exact hmom N (le_trans (le_max_left _ _) hN) _ (filter_subset _ _) _ (fun _ _ => by simp) a b hab
    (by linarith) fun t ht => hpt N (le_trans (le_max_right _ _) hN) t (le_trans ha ht.1) (le_trans ht.2 hb)

end ShortSieveHarman
