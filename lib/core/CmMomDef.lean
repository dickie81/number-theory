import CmLhD

/-! # Moments of the piecewise model: definitions -/

namespace CmMom

open CmPoly CmW CmNu CmLhD

/-- numerator of the floor at grid `2^-128` -/
def fl (q : ℚ) : ℤ := ⌊q * 2 ^ 128⌋

/-- local moment `∫_{piece p} hev (LD p) s · s^{2j}` -/
def mP (p j : ℕ) : ℚ := pmom 1 (LD p) (2 * j) (al p) (be p)

/-- global moment `∫₀¹ hev GD (s²) · s^{2j}` -/
def mG (j : ℕ) : ℚ := pmom 2 GD (2 * j) 0 1

def cs (c : ℕ) : List ℤ := (List.range 134).map fun j => ((List.range 16).map fun i => fl (mP (16 * c + i) j)).sum

def gs : List ℤ := (List.range 134).map fun j => fl (mG j)

end CmMom
