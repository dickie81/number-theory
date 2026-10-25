/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 165–168 of 1732

File 41 of 430: the parts `rows22310R_165` … `rows22310R_168` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 70 columns 0–34, row 70 columns 35–43, row 70 columns 44–49,
row 70 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_165 : rowsJ2 70 71 0 35 ≤ 959703447705981 := by decide +kernel

theorem rows22310R_166 : rowsJ2 70 71 35 44 ≤ 229653712881558 := by decide +kernel

theorem rows22310R_167 : rowsJ2 70 71 44 50 ≤ 105823584946913 := by decide +kernel

theorem rows22310R_168 : rowsJ2 70 71 50 55 ≤ 105003531315065 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_165
#print axioms SieveCert.rows22310R_168
