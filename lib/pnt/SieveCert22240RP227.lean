/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2654–2666 of 5066

File 227 of 387: the parts `rows22240R_2654` … `rows22240R_2666` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 98530 in units of a depth-4 test: row 97 columns 87–87, row 97 columns
88–88, row 97 columns 89–89, row 97 columns 90–90, row 97 columns 91–91, row 97 columns 92–92, row 97 columns 93–93,
row 97 columns 94–94, row 97 columns 95–95, row 97 columns 96–96, row 97 columns 97–339, row 98 columns 0–15, row 98
columns 16–21), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2654 : rowsJ2 97 98 87 88 ≤ 2811251758207 := by decide +kernel

theorem rows22240R_2655 : rowsJ2 97 98 88 89 ≤ 2790238764766 := by decide +kernel

theorem rows22240R_2656 : rowsJ2 97 98 89 90 ≤ 2844792966421 := by decide +kernel

theorem rows22240R_2657 : rowsJ2 97 98 90 91 ≤ 2993412842320 := by decide +kernel

theorem rows22240R_2658 : rowsJ2 97 98 91 92 ≤ 3221683989256 := by decide +kernel

theorem rows22240R_2659 : rowsJ2 97 98 92 93 ≤ 3548725197303 := by decide +kernel

theorem rows22240R_2660 : rowsJ2 97 98 93 94 ≤ 3915686153177 := by decide +kernel

theorem rows22240R_2661 : rowsJ2 97 98 94 95 ≤ 4384670037267 := by decide +kernel

theorem rows22240R_2662 : rowsJ2 97 98 95 96 ≤ 4895897793594 := by decide +kernel

theorem rows22240R_2663 : rowsJ2 97 98 96 97 ≤ 5513001020819 := by decide +kernel

theorem rows22240R_2664 : rowsJ2 97 98 97 340 ≤ 6175369233069 := by decide +kernel

theorem rows22240R_2665 : rowsJ2 98 99 0 16 ≤ 0 := by decide +kernel

theorem rows22240R_2666 : rowsJ2 98 99 16 22 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2654
#print axioms SieveCert.rows22240R_2666
