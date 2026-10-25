/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 44–47 of 1732

File 11 of 430: the parts `rows22310R_44` … `rows22310R_47` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27745 tests: row 48 columns 44–399, row 49 columns 0–34, row 49 columns
35–43, row 49 columns 44–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_44 : rowsJ2 48 49 44 400 ≤ 299455632229819 := by decide +kernel

theorem rows22310R_45 : rowsJ2 49 50 0 35 ≤ 1346339137131511 := by decide +kernel

theorem rows22310R_46 : rowsJ2 49 50 35 44 ≤ 669010743703215 := by decide +kernel

theorem rows22310R_47 : rowsJ2 49 50 44 400 ≤ 334756113537617 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_44
#print axioms SieveCert.rows22310R_47
