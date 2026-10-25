/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 703–706 of 1732

File 177 of 430: the parts `rows22310R_703` … `rows22310R_706` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26031 tests: row 116 columns 112–114, row 116 columns 115–399, row 117
columns 0–34, row 117 columns 35–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_703 : rowsJ2 116 117 112 115 ≤ 11287813593686 := by decide +kernel

theorem rows22310R_704 : rowsJ2 116 117 115 400 ≤ 10446776218154 := by decide +kernel

theorem rows22310R_705 : rowsJ2 117 118 0 35 ≤ 92076356271415 := by decide +kernel

theorem rows22310R_706 : rowsJ2 117 118 35 46 ≤ 257236329267197 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_703
#print axioms SieveCert.rows22310R_706
