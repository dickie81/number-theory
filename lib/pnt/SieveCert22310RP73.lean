/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 293–296 of 1732

File 73 of 430: the parts `rows22310R_293` … `rows22310R_296` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28119 tests: row 84 columns 66–74, row 84 columns 75–399, row 85 columns
0–34, row 85 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_293 : rowsJ2 84 85 66 75 ≤ 245096884120904 := by decide +kernel

theorem rows22310R_294 : rowsJ2 84 85 75 400 ≤ 190998939629395 := by decide +kernel

theorem rows22310R_295 : rowsJ2 85 86 0 35 ≤ 585252012278954 := by decide +kernel

theorem rows22310R_296 : rowsJ2 85 86 35 44 ≤ 69064025596874 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_293
#print axioms SieveCert.rows22310R_296
