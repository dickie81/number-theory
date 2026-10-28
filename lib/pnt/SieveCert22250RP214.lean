/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2634–2651 of 4715

File 214 of 351: the parts `rows22250R_2634` … `rows22250R_2651` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, work 95906 in units of a depth-4 test: row 100 columns 86–86, row 100
columns 87–87, row 100 columns 88–88, row 100 columns 89–89, row 100 columns 90–90, row 100 columns 91–91, row 100
columns 92–92, row 100 columns 93–93, row 100 columns 94–94, row 100 columns 95–95, row 100 columns 96–96, row 100
columns 97–97, row 100 columns 98–98, row 100 columns 99–99, row 100 columns 100–339, row 101 columns 0–18, row 101
columns 19–30, row 101 columns 31–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2634 : rowsJ2 100 101 86 87 ≤ 1484349144619 := by decide +kernel

theorem rows22250R_2635 : rowsJ2 100 101 87 88 ≤ 1519386148703 := by decide +kernel

theorem rows22250R_2636 : rowsJ2 100 101 88 89 ≤ 1636178517561 := by decide +kernel

theorem rows22250R_2637 : rowsJ2 100 101 89 90 ≤ 1854968504075 := by decide +kernel

theorem rows22250R_2638 : rowsJ2 100 101 90 91 ≤ 2114690505166 := by decide +kernel

theorem rows22250R_2639 : rowsJ2 100 101 91 92 ≤ 2479681612308 := by decide +kernel

theorem rows22250R_2640 : rowsJ2 100 101 92 93 ≤ 2889432128889 := by decide +kernel

theorem rows22250R_2641 : rowsJ2 100 101 93 94 ≤ 3408395146409 := by decide +kernel

theorem rows22250R_2642 : rowsJ2 100 101 94 95 ≤ 3975087884796 := by decide +kernel

theorem rows22250R_2643 : rowsJ2 100 101 95 96 ≤ 4655483872306 := by decide +kernel

theorem rows22250R_2644 : rowsJ2 100 101 96 97 ≤ 5387088918315 := by decide +kernel

theorem rows22250R_2645 : rowsJ2 100 101 97 98 ≤ 6237491396001 := by decide +kernel

theorem rows22250R_2646 : rowsJ2 100 101 98 99 ≤ 7143148877058 := by decide +kernel

theorem rows22250R_2647 : rowsJ2 100 101 99 100 ≤ 8173367557787 := by decide +kernel

theorem rows22250R_2648 : rowsJ2 100 101 100 340 ≤ 9263522041243 := by decide +kernel

theorem rows22250R_2649 : rowsJ2 101 102 0 19 ≤ 0 := by decide +kernel

theorem rows22250R_2650 : rowsJ2 101 102 19 31 ≤ 1788558343732 := by decide +kernel

theorem rows22250R_2651 : rowsJ2 101 102 31 34 ≤ 11188313124233 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2634
#print axioms SieveCert.rows22250R_2651
