/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 317–320 of 1732

File 79 of 430: the parts `rows22310R_317` … `rows22310R_320` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26400 tests: row 87 columns 69–82, row 87 columns 83–399, row 88 columns
0–34, row 88 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_317 : rowsJ2 87 88 69 83 ≤ 279772714991824 := by decide +kernel

theorem rows22310R_318 : rowsJ2 87 88 83 400 ≤ 62333029503126 := by decide +kernel

theorem rows22310R_319 : rowsJ2 88 89 0 35 ≤ 509247189943318 := by decide +kernel

theorem rows22310R_320 : rowsJ2 88 89 35 44 ≤ 58864595219747 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_317
#print axioms SieveCert.rows22310R_320
