import Mathlib
import CmW

/-! # Moments of the piecewise model and the quadrature values — computational definitions -/

namespace CmNu

open CmPoly CmBessel CmW

/-- `[(β^{m+i} − α^{m+i})/(m+i)]_{i<L}` with running powers `bx = β^m`, `by = α^m`. -/
def ml (x y : ℚ) : ℚ → ℚ → ℕ → ℕ → List ℚ
  | _, _, _, 0 => []
  | bx, byy, m, L + 1 => (bx - byy) / m :: ml x y (bx * x) (byy * y) (m + 1) L

def vloc : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: L, M => padd (psc a M) (vloc L M.tail)

def vglob : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: G, M => padd (psc a M) (vglob G M.tail.tail)

def JM : ℕ := 267
def al (p : ℕ) : ℚ := p / NP
def be (p : ℕ) : ℚ := (p + 1) / NP

def Mp (p : ℕ) : List ℚ := ml (be p) (al p) (be p) (al p) 1 (JM + dd + 2)
def M0 : List ℚ := ml 1 0 1 0 1 (JM + 2 * Gh.length + 2)

def vL : List ℚ := (List.range NP).foldr (fun p acc => padd (vloc (Lh p) (Mp p)) acc) []
def nu : List ℚ := padd (vglob Gh M0) (psc (-1) vL)
def nuh : List ℚ := ((List.range JM).map fun j => nu.getD j 0).map (rnd P)

end CmNu
