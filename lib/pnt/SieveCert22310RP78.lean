/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 313–316 of 1732

File 78 of 430: the parts `rows22310R_313` … `rows22310R_316` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29600 tests: row 87 columns 44–49, row 87 columns 50–54, row 87 columns
55–60, row 87 columns 61–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_313 : rowsJ2 87 88 44 50 ≤ 101270706084102 := by decide +kernel

theorem rows22310R_314 : rowsJ2 87 88 50 55 ≤ 168066659228084 := by decide +kernel

theorem rows22310R_315 : rowsJ2 87 88 55 61 ≤ 214845850496137 := by decide +kernel

theorem rows22310R_316 : rowsJ2 87 88 61 69 ≤ 236429210960973 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_313
#print axioms SieveCert.rows22310R_316
