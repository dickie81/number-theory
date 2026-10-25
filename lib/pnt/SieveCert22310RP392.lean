/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1557–1560 of 1732

File 392 of 430: the parts `rows22310R_1557` … `rows22310R_1560` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24106 tests: row 190 columns 64–399, row 191 columns 0–45, row 191 columns
46–51, row 191 columns 52–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1557 : rowsJ2 190 191 64 400 ≤ 2086391089177770 := by decide +kernel

theorem rows22310R_1558 : rowsJ2 191 192 0 46 ≤ 29584934500936 := by decide +kernel

theorem rows22310R_1559 : rowsJ2 191 192 46 52 ≤ 51648678321540 := by decide +kernel

theorem rows22310R_1560 : rowsJ2 191 192 52 57 ≤ 58014179520124 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1557
#print axioms SieveCert.rows22310R_1560
