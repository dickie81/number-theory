/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 591–597 of 5066

File 60 of 387: the parts `rows22240R_591` … `rows22240R_597` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 93780 in units of a depth-4 test: row 51 columns 32–32, row 51 columns
33–33, row 51 columns 34–34, row 51 columns 35–35, row 51 columns 36–36, row 51 columns 37–37, row 51 columns
38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22240R_591 : rowsJ2 51 52 32 33 ≤ 91570365327 := by decide +kernel

theorem rows22240R_592 : rowsJ2 51 52 33 34 ≤ 72885951799 := by decide +kernel

theorem rows22240R_593 : rowsJ2 51 52 34 35 ≤ 54342313407 := by decide +kernel

theorem rows22240R_594 : rowsJ2 51 52 35 36 ≤ 40171376169 := by decide +kernel

theorem rows22240R_595 : rowsJ2 51 52 36 37 ≤ 26088189139 := by decide +kernel

theorem rows22240R_596 : rowsJ2 51 52 37 38 ≤ 17011718053 := by decide +kernel

theorem rows22240R_597 : rowsJ2 51 52 38 39 ≤ 7976986000 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_591
#print axioms SieveCert.rows22240R_597
