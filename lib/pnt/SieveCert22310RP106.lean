/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 421–424 of 1732

File 106 of 430: the parts `rows22310R_421` … `rows22310R_424` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29341 tests: row 99 columns 51–59, row 99 columns 60–78, row 99 columns
79–85, row 99 columns 86–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_421 : rowsJ2 99 100 51 60 ≤ 250876591378235 := by decide +kernel

theorem rows22310R_422 : rowsJ2 99 100 60 79 ≤ 299744722447718 := by decide +kernel

theorem rows22310R_423 : rowsJ2 99 100 79 86 ≤ 43494740257465 := by decide +kernel

theorem rows22310R_424 : rowsJ2 99 100 86 90 ≤ 13282077120665 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_421
#print axioms SieveCert.rows22310R_424
