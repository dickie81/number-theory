/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 321–324 of 1732

File 80 of 430: the parts `rows22310R_321` … `rows22310R_324` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28895 tests: row 88 columns 44–49, row 88 columns 50–54, row 88 columns
55–60, row 88 columns 61–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_321 : rowsJ2 88 89 44 50 ≤ 106746954944453 := by decide +kernel

theorem rows22310R_322 : rowsJ2 88 89 50 55 ≤ 172783447084206 := by decide +kernel

theorem rows22310R_323 : rowsJ2 88 89 55 61 ≤ 209906295538161 := by decide +kernel

theorem rows22310R_324 : rowsJ2 88 89 61 69 ≤ 229498781641183 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_321
#print axioms SieveCert.rows22310R_324
