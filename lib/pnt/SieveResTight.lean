/-
# The resonant window's condition on a box with the variable tied to the rest

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

`SieveTypeIIHM.ResBox g L K m_lo lo` asks the window's condition `ResCond` at every exponent `m ≥ m_lo` of the
variable and every exponents `s j ≥ lo j` of the rest: on a box of cells it is tested at a corner that is no point of
the box, the rest's lower ends with the variable that the rest's upper ends leave. On a box the rest and the variable
make up `q^L`, so the variable's exponent is `L − Σ_j s_j` up to the dyadic blocks.

* `ResBoxT g L K lo hi w`, **the condition on a box, the variable tied to the rest**: `ResCond` at every exponents
  `lo j ≤ s j ≤ hi j` of the rest and every `m` with `L − w ≤ Σ_j s_j + m ≤ L + 10⁻⁵`.

The file imports `SieveResFull.lean`.
-/
import SieveResFull

open Real Finset

namespace SieveTypeIIHM

/-- **The resonant window's condition on a box, the variable tied to the rest**: `ResCond` at every exponents
`lo j ≤ s j ≤ hi j` of the rest and every exponent `m` of the variable with `L − w ≤ Σ_j s_j + m ≤ L + 10⁻⁵`. -/
def ResBoxT (g : ℝ → ℝ) (L : ℝ) (K : ℕ) (lo hi : ℕ → ℝ) (w : ℝ) : Prop :=
  ∀ (m : ℝ) (s : ℕ → ℝ), (∀ j < K, lo j ≤ s j ∧ s j ≤ hi j) → L - w ≤ ∑ j ∈ Finset.range K, s j + m →
    ∑ j ∈ Finset.range K, s j + m ≤ L + 1 / 10 ^ 5 → ResCond g L K m s

end SieveTypeIIHM
