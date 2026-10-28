/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 621–627 of 5066

File 63 of 387: the parts `rows22240R_621` … `rows22240R_627` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 90269 in units of a depth-4 test: row 52 columns 30–30, row 52 columns
31–31, row 52 columns 32–32, row 52 columns 33–33, row 52 columns 34–34, row 52 columns 35–35, row 52 columns
36–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_621 : rowsJ2 52 53 30 31 ≤ 113723652544 := by decide +kernel

theorem rows22240R_622 : rowsJ2 52 53 31 32 ≤ 90583537608 := by decide +kernel

theorem rows22240R_623 : rowsJ2 52 53 32 33 ≤ 72450788162 := by decide +kernel

theorem rows22240R_624 : rowsJ2 52 53 33 34 ≤ 53852261872 := by decide +kernel

theorem rows22240R_625 : rowsJ2 52 53 34 35 ≤ 40257238654 := by decide +kernel

theorem rows22240R_626 : rowsJ2 52 53 35 36 ≤ 26140027159 := by decide +kernel

theorem rows22240R_627 : rowsJ2 52 53 36 37 ≤ 17043024646 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_621
#print axioms SieveCert.rows22240R_627
