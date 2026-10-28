/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2624–2640 of 5066

File 225 of 387: the parts `rows22240R_2624` … `rows22240R_2640` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 99753 in units of a depth-4 test: row 97 columns 36–37, row 97 columns
38–38, row 97 columns 39–39, row 97 columns 40–40, row 97 columns 41–41, row 97 columns 42–42, row 97 columns 43–43,
row 97 columns 44–44, row 97 columns 45–45, row 97 columns 46–46, row 97 columns 47–47, row 97 columns 48–48, row 97
columns 49–49, row 97 columns 50–50, row 97 columns 51–52, row 97 columns 53–54, row 97 columns 55–56), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2624 : rowsJ2 97 98 36 38 ≤ 15157171056289 := by decide +kernel

theorem rows22240R_2625 : rowsJ2 97 98 38 39 ≤ 9942471377335 := by decide +kernel

theorem rows22240R_2626 : rowsJ2 97 98 39 40 ≤ 11504327128157 := by decide +kernel

theorem rows22240R_2627 : rowsJ2 97 98 40 41 ≤ 13073203140804 := by decide +kernel

theorem rows22240R_2628 : rowsJ2 97 98 41 42 ≤ 14646507650726 := by decide +kernel

theorem rows22240R_2629 : rowsJ2 97 98 42 43 ≤ 15988806867533 := by decide +kernel

theorem rows22240R_2630 : rowsJ2 97 98 43 44 ≤ 15690827220624 := by decide +kernel

theorem rows22240R_2631 : rowsJ2 97 98 44 45 ≤ 13925828537070 := by decide +kernel

theorem rows22240R_2632 : rowsJ2 97 98 45 46 ≤ 12240871885207 := by decide +kernel

theorem rows22240R_2633 : rowsJ2 97 98 46 47 ≤ 10574781088194 := by decide +kernel

theorem rows22240R_2634 : rowsJ2 97 98 47 48 ≤ 8986858736613 := by decide +kernel

theorem rows22240R_2635 : rowsJ2 97 98 48 49 ≤ 7513804130871 := by decide +kernel

theorem rows22240R_2636 : rowsJ2 97 98 49 50 ≤ 6212218560649 := by decide +kernel

theorem rows22240R_2637 : rowsJ2 97 98 50 51 ≤ 5078846807986 := by decide +kernel

theorem rows22240R_2638 : rowsJ2 97 98 51 53 ≤ 7328109426719 := by decide +kernel

theorem rows22240R_2639 : rowsJ2 97 98 53 55 ≤ 4056092477671 := by decide +kernel

theorem rows22240R_2640 : rowsJ2 97 98 55 57 ≤ 1167177937526 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2624
#print axioms SieveCert.rows22240R_2640
