/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1538–1540 of 1732

File 387 of 430: the parts `rows22310R_1538` … `rows22310R_1540` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22511 tests: row 187 columns 0–47, row 187 columns 48–53, row 187 columns
54–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1538 : rowsJ2 187 188 0 48 ≤ 33829721084102 := by decide +kernel

theorem rows22310R_1539 : rowsJ2 187 188 48 54 ≤ 48409067037280 := by decide +kernel

theorem rows22310R_1540 : rowsJ2 187 188 54 59 ≤ 54420618717778 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1538
#print axioms SieveCert.rows22310R_1540
