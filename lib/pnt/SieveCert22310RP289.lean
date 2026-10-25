/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1151–1154 of 1732

File 289 of 430: the parts `rows22310R_1151` … `rows22310R_1154` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27600 tests: row 144 columns 77–79, row 144 columns 80–82, row 144 columns
83–85, row 144 columns 86–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1151 : rowsJ2 144 145 77 80 ≤ 7106058068955 := by decide +kernel

theorem rows22310R_1152 : rowsJ2 144 145 80 83 ≤ 3899215819407 := by decide +kernel

theorem rows22310R_1153 : rowsJ2 144 145 83 86 ≤ 1356491958546 := by decide +kernel

theorem rows22310R_1154 : rowsJ2 144 145 86 89 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1151
#print axioms SieveCert.rows22310R_1154
