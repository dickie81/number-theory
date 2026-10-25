/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 305–308 of 1732

File 76 of 430: the parts `rows22310R_305` … `rows22310R_308` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28556 tests: row 86 columns 44–49, row 86 columns 50–54, row 86 columns
55–59, row 86 columns 60–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_305 : rowsJ2 86 87 44 50 ≤ 96358491942415 := by decide +kernel

theorem rows22310R_306 : rowsJ2 86 87 50 55 ≤ 163291274693071 := by decide +kernel

theorem rows22310R_307 : rowsJ2 86 87 55 60 ≤ 185317410226061 := by decide +kernel

theorem rows22310R_308 : rowsJ2 86 87 60 67 ≤ 222356005663476 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_305
#print axioms SieveCert.rows22310R_308
