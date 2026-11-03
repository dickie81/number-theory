import Mathlib
import CmPoly
import DigammaStirling

/-! # Piecewise-polynomial model of `wψ(30 s)` on `[0,1]` — computational definitions -/

namespace CmW

open CmPoly CmBessel WeilConst

def P : ℕ := 128
def NP : ℕ := 128
def dd : ℕ := 20
def aN : ℚ := 193 / 4
def kv : ℚ := (15 / aN) ^ 2
def L1 : ℕ := 14
def L3 : ℕ := 12
def K2 : ℕ := 45

def lam : ℚ := rnd 64 L2lo
def elam : ℚ := (L2hi - L2lo) + 1 / 2 ^ 64
def kap : ℚ := rnd 64 (s2lo * L2lo)
def ekap : ℚ := (s2hi * L2hi - s2lo * L2lo) + 1 / 2 ^ 64

def xA : ℚ := 1 - 193 / 128
def la_lo : ℚ := 5 * L2lo - Ls xA 60 - Lr xA 60
def la_hi : ℚ := 5 * L2hi - Ls xA 60 + Lr xA 60
def xP1 : ℚ := 1 - plo / 2
def xP2 : ℚ := 1 - phi / 2
def lp_lo : ℚ := L2lo - Ls xP1 70 - Lr xP1 70
def lp_hi : ℚ := L2hi - Ls xP2 70 + Lr xP2 70
def K0lo : ℚ := la_lo - lp_hi - βhi
def K0hi : ℚ := la_hi - lp_lo - βlo
def K0h : ℚ := rnd P K0lo
def eK : ℚ := (K0hi - K0lo) + 1 / 2 ^ P

def glog : List ℚ := 0 :: (List.range L1).map fun i : ℕ => -(1 / 2) * (-kv) ^ (i + 1) / ((i:ℚ) + 1)
def gv : List ℚ := (List.range L3).map fun i : ℕ => (-kv) ^ i
def ginv : List ℚ := psc (1 / (12 * aN ^ 2)) (pmul [1, -kv] (pmul gv gv))
def gcos : List ℚ := (List.range K2).map fun k : ℕ => (-1) ^ k * (30 * lam) ^ (2 * k) / ((2 * k).factorial : ℚ)
def Gu : List ℚ := padd [K0h] (padd glog (padd (psc (-1) ginv) (psc (-kap) gcos)))
def Gh : List ℚ := Gu.map (rnd P)

def E48 : ℚ := 1 / (120 * aN ^ 4)
def eG : ℚ := (1 / 2) * kv ^ (L1 + 1) / (1 - kv) + 5 * kv ^ L3 / (12 * aN ^ 2) + ekap
  + kap * (30 * elam + 2 * (30 * lam) ^ (2 * K2) / ((2 * K2).factorial : ℚ)) + eK + Gu.length / 2 ^ P + E48

/-! ## Local (piecewise) part -/

def mulG (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def glist (m : ℚ × ℚ) : ℚ × ℚ → ℕ → List ℚ
  | _, 0 => []
  | u, d + 1 => u.1 :: glist m (mulG u m) d

def nrm (c b0 : ℚ) : ℚ := c ^ 2 + b0 ^ 2
def gterm (c b0 : ℚ) : List ℚ := glist (-b0 / nrm c b0, -c / nrm c b0) (c / nrm c b0, -b0 / nrm c b0) dd

/-- weights and centres: `½·Re 1/(a+ib)` and `Re 1/(k+¼+ib)`, `k < 48`. -/
def taus : List (ℚ × ℚ) := (1 / 2, aN) :: (List.range 48).map fun k : ℕ => ((1:ℚ), (k:ℚ) + 1 / 4)

def s0 (p : ℕ) : ℚ := (2 * p + 1) / (2 * NP)
def rr : ℚ := 15 / (2 * NP)

def Lex (p : ℕ) : List ℚ :=
  taus.foldr (fun τ acc => padd ((psc τ.1 (gterm τ.2 (15 * s0 p))).map (rnd P)) acc) []
def Lh (p : ℕ) : List ℚ := (paff (-15 * s0 p) 15 (Lex p)).map (rnd P)

def eL (p : ℕ) : ℚ :=
  (taus.map fun τ => τ.1 * rr ^ dd / (nrm τ.2 (15 * s0 p) ^ (dd / 2) * τ.2)).sum
    + taus.length * dd / 2 ^ P + (paff (-15 * s0 p) 15 (Lex p)).length / 2 ^ P

def epw (p : ℕ) : ℚ := eG + eL p

end CmW
