/-
# The half-plane `Re s > 11/12` in the prime number theorem

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`).

Plain statement. `ψ(x) − x = O(x^{11/12+ε})` for every `ε > 0`, with no hypothesis
(`psi_isBigO_eleven_twelfths`): `psi_isBigO_of_zeroFree` at the half-plane `Re s > 11/12`
(`Eis.ne_zero_of_re_gt_eleven_twelfths`, `lib/core/KubotaThetaProof.lean`).
-/
import HalfPlanePNT
import KubotaThetaProof

open Asymptotics Filter
open scoped Chebyshev

namespace HalfPlanePNT

/-- **The prime number theorem with error `O(x^{11/12+ε})`**, with no hypothesis:
`psi_isBigO_of_zeroFree` at the half-plane `Re s > 11/12`. -/
theorem psi_isBigO_eleven_twelfths {ε : ℝ} (hε : 0 < ε) :
    (ψ - id) =O[atTop] fun x : ℝ ↦ x ^ ((11 : ℝ) / 12 + ε) :=
  psi_isBigO_of_zeroFree (by norm_num) (fun _ hs ↦ (Eis.ne_zero_of_re_gt_eleven_twelfths hs).1) hε

end HalfPlanePNT
