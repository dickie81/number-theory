/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 301–304 of 1732

File 75 of 430: the parts `rows22310R_301` … `rows22310R_304` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27110 tests: row 85 columns 67–76, row 85 columns 77–399, row 86 columns
0–34, row 86 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_301 : rowsJ2 85 86 67 77 ≤ 250521981811793 := by decide +kernel

theorem rows22310R_302 : rowsJ2 85 86 77 400 ≤ 153638680616818 := by decide +kernel

theorem rows22310R_303 : rowsJ2 86 87 0 35 ≤ 559703276632133 := by decide +kernel

theorem rows22310R_304 : rowsJ2 86 87 35 44 ≤ 64794639712530 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_301
#print axioms SieveCert.rows22310R_304
