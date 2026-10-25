/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 558–561 of 1732

File 141 of 430: the parts `rows22310R_558` … `rows22310R_561` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23623 tests: row 108 columns 106–107, row 108 columns 108–399, row 109
columns 0–34, row 109 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_558 : rowsJ2 108 109 106 108 ≤ 3104420916844 := by decide +kernel

theorem rows22310R_559 : rowsJ2 108 109 108 400 ≤ 1715667971387 := by decide +kernel

theorem rows22310R_560 : rowsJ2 109 110 0 35 ≤ 127370278580278 := by decide +kernel

theorem rows22310R_561 : rowsJ2 109 110 35 44 ≤ 176472901660839 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_558
#print axioms SieveCert.rows22310R_561
