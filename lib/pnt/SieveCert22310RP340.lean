/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1355–1358 of 1732

File 340 of 430: the parts `rows22310R_1355` … `rows22310R_1358` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24538 tests: row 161 columns 92–399, row 162 columns 0–56, row 162 columns
57–61, row 162 columns 62–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1355 : rowsJ2 161 162 92 400 ≤ 391768630614687 := by decide +kernel

theorem rows22310R_1356 : rowsJ2 162 163 0 57 ≤ 108831817917071 := by decide +kernel

theorem rows22310R_1357 : rowsJ2 162 163 57 62 ≤ 18083142426685 := by decide +kernel

theorem rows22310R_1358 : rowsJ2 162 163 62 66 ≤ 23408687526942 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1355
#print axioms SieveCert.rows22310R_1358
