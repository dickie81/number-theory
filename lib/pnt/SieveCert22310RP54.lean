/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 217–220 of 1732

File 54 of 430: the parts `rows22310R_217` … `rows22310R_220` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 76 columns 0–34, row 76 columns 35–43, row 76 columns 44–49,
row 76 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22310R_217 : rowsJ2 76 77 0 35 ≤ 814897063544928 := by decide +kernel

theorem rows22310R_218 : rowsJ2 76 77 35 44 ≤ 145288902969433 := by decide +kernel

theorem rows22310R_219 : rowsJ2 76 77 44 50 ≤ 84068599756429 := by decide +kernel

theorem rows22310R_220 : rowsJ2 76 77 50 55 ≤ 111145284257918 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_217
#print axioms SieveCert.rows22310R_220
