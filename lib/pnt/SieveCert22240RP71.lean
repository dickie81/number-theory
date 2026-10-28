/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 698–708 of 5066

File 71 of 387: the parts `rows22240R_698` … `rows22240R_708` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 93213 in units of a depth-4 test: row 54 columns 42–42, row 54 columns
43–43, row 54 columns 44–44, row 54 columns 45–45, row 54 columns 46–46, row 54 columns 47–47, row 54 columns 48–48,
row 54 columns 49–49, row 54 columns 50–50, row 54 columns 51–51, row 54 columns 52–52), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_698 : rowsJ2 54 55 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_699 : rowsJ2 54 55 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_700 : rowsJ2 54 55 44 45 ≤ 74134199933 := by decide +kernel

theorem rows22240R_701 : rowsJ2 54 55 45 46 ≤ 216801176414 := by decide +kernel

theorem rows22240R_702 : rowsJ2 54 55 46 47 ≤ 422792675573 := by decide +kernel

theorem rows22240R_703 : rowsJ2 54 55 47 48 ≤ 902697529139 := by decide +kernel

theorem rows22240R_704 : rowsJ2 54 55 48 49 ≤ 1724603407796 := by decide +kernel

theorem rows22240R_705 : rowsJ2 54 55 49 50 ≤ 2659564793846 := by decide +kernel

theorem rows22240R_706 : rowsJ2 54 55 50 51 ≤ 3628956103676 := by decide +kernel

theorem rows22240R_707 : rowsJ2 54 55 51 52 ≤ 4774797223454 := by decide +kernel

theorem rows22240R_708 : rowsJ2 54 55 52 53 ≤ 6240870382975 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_698
#print axioms SieveCert.rows22240R_708
