/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1728–1736 of 5066

File 158 of 387: the parts `rows22240R_1728` … `rows22240R_1736` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (9 parts, work 91838 in units of a depth-4 test: row 77 columns 50–50, row 77 columns
51–51, row 77 columns 52–52, row 77 columns 53–53, row 77 columns 54–54, row 77 columns 55–55, row 77 columns 56–56,
row 77 columns 57–57, row 77 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_1728 : rowsJ2 77 78 50 51 ≤ 2150071656286 := by decide +kernel

theorem rows22240R_1729 : rowsJ2 77 78 51 52 ≤ 2385911726022 := by decide +kernel

theorem rows22240R_1730 : rowsJ2 77 78 52 53 ≤ 2636551009130 := by decide +kernel

theorem rows22240R_1731 : rowsJ2 77 78 53 54 ≤ 2590023883262 := by decide +kernel

theorem rows22240R_1732 : rowsJ2 77 78 54 55 ≤ 2368296229374 := by decide +kernel

theorem rows22240R_1733 : rowsJ2 77 78 55 56 ≤ 2141444844519 := by decide +kernel

theorem rows22240R_1734 : rowsJ2 77 78 56 57 ≤ 1916966119747 := by decide +kernel

theorem rows22240R_1735 : rowsJ2 77 78 57 58 ≤ 1686980972242 := by decide +kernel

theorem rows22240R_1736 : rowsJ2 77 78 58 59 ≤ 1459180492694 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1728
#print axioms SieveCert.rows22240R_1736
