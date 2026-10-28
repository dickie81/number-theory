/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2698–2710 of 5066

File 230 of 387: the parts `rows22240R_2698` … `rows22240R_2710` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 92285 in units of a depth-4 test: row 98 columns 86–86, row 98 columns
87–87, row 98 columns 88–88, row 98 columns 89–89, row 98 columns 90–90, row 98 columns 91–91, row 98 columns 92–92,
row 98 columns 93–93, row 98 columns 94–94, row 98 columns 95–95, row 98 columns 96–96, row 98 columns 97–97, row 98
columns 98–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_2698 : rowsJ2 98 99 86 87 ≤ 2546523326019 := by decide +kernel

theorem rows22240R_2699 : rowsJ2 98 99 87 88 ≤ 2488045483125 := by decide +kernel

theorem rows22240R_2700 : rowsJ2 98 99 88 89 ≤ 2521630765214 := by decide +kernel

theorem rows22240R_2701 : rowsJ2 98 99 89 90 ≤ 2633011312250 := by decide +kernel

theorem rows22240R_2702 : rowsJ2 98 99 90 91 ≤ 2840715271653 := by decide +kernel

theorem rows22240R_2703 : rowsJ2 98 99 91 92 ≤ 3130608825831 := by decide +kernel

theorem rows22240R_2704 : rowsJ2 98 99 92 93 ≤ 3477266708346 := by decide +kernel

theorem rows22240R_2705 : rowsJ2 98 99 93 94 ≤ 3909052281651 := by decide +kernel

theorem rows22240R_2706 : rowsJ2 98 99 94 95 ≤ 4400125393263 := by decide +kernel

theorem rows22240R_2707 : rowsJ2 98 99 95 96 ≤ 4979854859312 := by decide +kernel

theorem rows22240R_2708 : rowsJ2 98 99 96 97 ≤ 5622098862761 := by decide +kernel

theorem rows22240R_2709 : rowsJ2 98 99 97 98 ≤ 6357388519262 := by decide +kernel

theorem rows22240R_2710 : rowsJ2 98 99 98 340 ≤ 7159068363480 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2698
#print axioms SieveCert.rows22240R_2710
