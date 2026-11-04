import Mathlib
import CmW

/-! # The pieces `[al p, be p] = [p/128, (p+1)/128]` of the model's grid on `[0, 1]` -/

namespace CmNu

open CmW

def al (p : ℕ) : ℚ := p / NP
def be (p : ℕ) : ℚ := (p + 1) / NP

end CmNu
