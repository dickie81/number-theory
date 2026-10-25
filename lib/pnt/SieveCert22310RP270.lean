/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1077–1080 of 1732

File 270 of 430: the parts `rows22310R_1077` … `rows22310R_1080` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27953 tests: row 138 columns 107–399, row 139 columns 0–47, row 139 columns
48–67, row 139 columns 68–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1077 : rowsJ2 138 139 107 400 ≤ 523954725221428 := by decide +kernel

theorem rows22310R_1078 : rowsJ2 139 140 0 48 ≤ 286002937141158 := by decide +kernel

theorem rows22310R_1079 : rowsJ2 139 140 48 68 ≤ 17877770866512 := by decide +kernel

theorem rows22310R_1080 : rowsJ2 139 140 68 73 ≤ 8357147275045 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1077
#print axioms SieveCert.rows22310R_1080
