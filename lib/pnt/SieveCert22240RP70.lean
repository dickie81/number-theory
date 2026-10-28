/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 689–697 of 5066

File 70 of 387: the parts `rows22240R_689` … `rows22240R_697` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 98517 in units of a depth-4 test: row 54 columns 33–33, row 54 columns
34–34, row 54 columns 35–35, row 54 columns 36–36, row 54 columns 37–37, row 54 columns 38–38, row 54 columns 39–39,
row 54 columns 40–40, row 54 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_689 : rowsJ2 54 55 33 34 ≤ 25661605652 := by decide +kernel

theorem rows22240R_690 : rowsJ2 54 55 34 35 ≤ 17118632736 := by decide +kernel

theorem rows22240R_691 : rowsJ2 54 55 35 36 ≤ 8023592421 := by decide +kernel

theorem rows22240R_692 : rowsJ2 54 55 36 37 ≤ 4005292366 := by decide +kernel

theorem rows22240R_693 : rowsJ2 54 55 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_694 : rowsJ2 54 55 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_695 : rowsJ2 54 55 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_696 : rowsJ2 54 55 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_697 : rowsJ2 54 55 41 42 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_689
#print axioms SieveCert.rows22240R_697
