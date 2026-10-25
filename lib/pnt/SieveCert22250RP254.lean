/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2786–2795 of 5796

File 254 of 465: the parts `rows22250R_2786` … `rows22250R_2795` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97117 tests: row 98 columns 94–94, row 98 columns 95–95, row 98 columns
96–96, row 98 columns 97–97, row 98 columns 98–359, row 99 columns 0–15, row 99 columns 16–19, row 99 columns 20–25,
row 99 columns 26–33, row 99 columns 34–36), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2786 : rowsJ2 98 99 94 95 ≤ 3754809060230 := by decide +kernel

theorem rows22250R_2787 : rowsJ2 98 99 95 96 ≤ 3649515506549 := by decide +kernel

theorem rows22250R_2788 : rowsJ2 98 99 96 97 ≤ 3615853997358 := by decide +kernel

theorem rows22250R_2789 : rowsJ2 98 99 97 98 ≤ 3639952808790 := by decide +kernel

theorem rows22250R_2790 : rowsJ2 98 99 98 360 ≤ 3737525761939 := by decide +kernel

theorem rows22250R_2791 : rowsJ2 99 100 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2792 : rowsJ2 99 100 16 20 ≤ 0 := by decide +kernel

theorem rows22250R_2793 : rowsJ2 99 100 20 26 ≤ 0 := by decide +kernel

theorem rows22250R_2794 : rowsJ2 99 100 26 34 ≤ 560107098194 := by decide +kernel

theorem rows22250R_2795 : rowsJ2 99 100 34 37 ≤ 6396269413763 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2786
#print axioms SieveCert.rows22250R_2795
