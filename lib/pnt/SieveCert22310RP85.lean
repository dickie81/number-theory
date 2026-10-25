/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 341–344 of 1732

File 85 of 430: the parts `rows22310R_341` … `rows22310R_344` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28590 tests: row 90 columns 72–86, row 90 columns 87–399, row 91 columns
0–34, row 91 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_341 : rowsJ2 90 91 72 87 ≤ 221873111508664 := by decide +kernel

theorem rows22310R_342 : rowsJ2 90 91 87 400 ≤ 33056395570549 := by decide +kernel

theorem rows22310R_343 : rowsJ2 91 92 0 35 ≤ 435645943942464 := by decide +kernel

theorem rows22310R_344 : rowsJ2 91 92 35 44 ≤ 56914721754608 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_341
#print axioms SieveCert.rows22310R_344
