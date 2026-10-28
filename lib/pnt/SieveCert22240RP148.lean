/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1587–1598 of 5066

File 148 of 387: the parts `rows22240R_1587` … `rows22240R_1598` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 95000 in units of a depth-4 test: row 74 columns 58–58, row 74 columns
59–59, row 74 columns 60–60, row 74 columns 61–61, row 74 columns 62–62, row 74 columns 63–63, row 74 columns 64–64,
row 74 columns 65–65, row 74 columns 66–66, row 74 columns 67–67, row 74 columns 68–68, row 74 columns 69–69), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1587 : rowsJ2 74 75 58 59 ≤ 2927277739690 := by decide +kernel

theorem rows22240R_1588 : rowsJ2 74 75 59 60 ≤ 2644039301663 := by decide +kernel

theorem rows22240R_1589 : rowsJ2 74 75 60 61 ≤ 2416675821099 := by decide +kernel

theorem rows22240R_1590 : rowsJ2 74 75 61 62 ≤ 2191513653978 := by decide +kernel

theorem rows22240R_1591 : rowsJ2 74 75 62 63 ≤ 2022396781834 := by decide +kernel

theorem rows22240R_1592 : rowsJ2 74 75 63 64 ≤ 1793576244453 := by decide +kernel

theorem rows22240R_1593 : rowsJ2 74 75 64 65 ≤ 1621482548601 := by decide +kernel

theorem rows22240R_1594 : rowsJ2 74 75 65 66 ≤ 1388471490058 := by decide +kernel

theorem rows22240R_1595 : rowsJ2 74 75 66 67 ≤ 1212919113642 := by decide +kernel

theorem rows22240R_1596 : rowsJ2 74 75 67 68 ≤ 975166584589 := by decide +kernel

theorem rows22240R_1597 : rowsJ2 74 75 68 69 ≤ 795655459571 := by decide +kernel

theorem rows22240R_1598 : rowsJ2 74 75 69 70 ≤ 552588096777 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1587
#print axioms SieveCert.rows22240R_1598
