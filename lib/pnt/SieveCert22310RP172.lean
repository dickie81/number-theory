/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 683–686 of 1732

File 172 of 430: the parts `rows22310R_683` … `rows22310R_686` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23709 tests: row 115 columns 109–111, row 115 columns 112–114, row 115
columns 115–399, row 116 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_683 : rowsJ2 115 116 109 112 ≤ 6751557223853 := by decide +kernel

theorem rows22310R_684 : rowsJ2 115 116 112 115 ≤ 10716443823065 := by decide +kernel

theorem rows22310R_685 : rowsJ2 115 116 115 400 ≤ 4657268930102 := by decide +kernel

theorem rows22310R_686 : rowsJ2 116 117 0 35 ≤ 92981027117477 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_683
#print axioms SieveCert.rows22310R_686
