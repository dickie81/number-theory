import Mathlib
import CmBessel

/-! # A small verified list-polynomial library over `ℚ` (Horner evaluation in `ℝ`) -/

namespace CmPoly

open Real Finset CmBessel

noncomputable def hev : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: l, x => (a : ℝ) + x * hev l x

def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

def psc (c : ℚ) (p : List ℚ) : List ℚ := p.map (c * ·)

def pmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => padd (psc a q) (0 :: pmul p q)

/-- `p(α + β x)`. -/
def paff (α β : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => padd [a] (pmul [α, β] (paff α β p))

lemma hev_padd (p q : List ℚ) (x : ℝ) : hev (padd p q) x = hev p x + hev q x := by
  induction p generalizing q with
  | nil => simp [padd, hev]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, hev]
    | cons b q => simp only [padd, hev, ih]; push_cast; ring

lemma hev_psc (c : ℚ) (p : List ℚ) (x : ℝ) : hev (psc c p) x = c * hev p x := by
  induction p with
  | nil => simp [psc, hev]
  | cons a p ih =>
    simp only [psc, List.map_cons, hev] at ih ⊢; rw [ih]; push_cast; ring

lemma hev_pmul (p q : List ℚ) (x : ℝ) : hev (pmul p q) x = hev p x * hev q x := by
  induction p with
  | nil => simp [pmul, hev]
  | cons a p ih => simp only [pmul, hev_padd, hev_psc, hev, ih]; push_cast; ring

lemma hev_paff (α β : ℚ) (p : List ℚ) (x : ℝ) : hev (paff α β p) x = hev p (α + β * x) := by
  induction p with
  | nil => simp [paff, hev]
  | cons a p ih => simp only [paff, hev_padd, hev_pmul, hev, ih]; push_cast; ring

lemma hev_sum (l : List ℚ) (x : ℝ) : hev l x = ∑ i ∈ range l.length, ((l.getD i 0 : ℚ) : ℝ) * x ^ i := by
  induction l with
  | nil => simp [hev]
  | cons a l ih =>
    rw [hev, ih, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1; apply sum_congr rfl; intro i _; ring

lemma hev_cont (l : List ℚ) : Continuous (hev l) := by
  have : hev l = fun x => ∑ i ∈ range l.length, ((l.getD i 0 : ℚ) : ℝ) * x ^ i := funext (hev_sum l)
  rw [this]; fun_prop

lemma hev_rnd (P : ℕ) (l : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |hev l x - hev (l.map (rnd P)) x| ≤ l.length / 2 ^ P := by
  induction l with
  | nil => simp [hev]
  | cons a l ih =>
    simp only [List.map_cons, hev, List.length_cons]
    have h1 := rnd_err P a
    have : |x * (hev l x - hev (l.map (rnd P)) x)| ≤ l.length / 2 ^ P := by
      rw [abs_mul]; calc |x| * _ ≤ 1 * (l.length / 2 ^ P) := mul_le_mul hx ih (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc |(a:ℝ) + x * hev l x - ((rnd P a : ℚ) + x * hev (l.map (rnd P)) x)|
        = |((a:ℝ) - rnd P a) + x * (hev l x - hev (l.map (rnd P)) x)| := by ring_nf
      _ ≤ 1 / 2 ^ P + l.length / 2 ^ P := (abs_add_le _ _).trans (add_le_add h1 this)
      _ = _ := by push_cast; ring

/-- `Σ |lᵢ|`, a bound for `|hev l x|` on `|x| ≤ 1`. -/
def pabs : List ℚ → ℚ
  | [] => 0
  | a :: l => |a| + pabs l

lemma hev_abs (l : List ℚ) {x : ℝ} (hx : |x| ≤ 1) : |hev l x| ≤ (pabs l : ℝ) := by
  induction l with
  | nil => simp [hev, pabs]
  | cons a l ih =>
    simp only [hev, pabs]; push_cast
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]; calc |x| * |hev l x| ≤ 1 * pabs l := mul_le_mul hx ih (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

/-! ## Moments `∫_α^β hev l (x^e) · x^j dx` -/

def lsum (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range n).map f).sum

/-- `∫_α^β (Σᵢ lᵢ x^{e·i}) x^j dx`. -/
def pmom (e : ℕ) (l : List ℚ) (j : ℕ) (α β : ℚ) : ℚ :=
  lsum l.length fun i => l.getD i 0 * (β ^ (e * i + j + 1) - α ^ (e * i + j + 1)) / (e * i + j + 1 : ℕ)

lemma pmom_eq (e : ℕ) (l : List ℚ) (j : ℕ) (α β : ℚ) :
    ∫ x in (α:ℝ)..β, hev l (x ^ e) * x ^ j = (pmom e l j α β : ℝ) := by
  have h : (fun x : ℝ => hev l (x ^ e) * x ^ j)
      = fun x => ∑ i ∈ range l.length, ((l.getD i 0 : ℚ) : ℝ) * x ^ (e * i + j) := by
    funext x; rw [hev_sum, sum_mul]; apply sum_congr rfl; intro i _; rw [← pow_mul, mul_assoc, ← pow_add]
  rw [h, intervalIntegral.integral_finsetSum (fun i _ => by apply Continuous.intervalIntegrable; fun_prop)]
  unfold pmom lsum; rw [WeilHead.cast_lsum]
  apply sum_congr rfl; intro i _
  rw [intervalIntegral.integral_const_mul, integral_pow]; push_cast; ring

end CmPoly
