/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3746–3759 of 5796

File 319 of 465: the parts `rows22250R_3746` … `rows22250R_3759` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97623 tests: row 121 columns 37–38, row 121 columns 39–40, row 121 columns
41–43, row 121 columns 44–48, row 121 columns 49–60, row 121 columns 61–65, row 121 columns 66–68, row 121 columns
69–70, row 121 columns 71–73, row 121 columns 74–76, row 121 columns 77–79, row 121 columns 80–82, row 121 columns
83–85, row 121 columns 86–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3746 : rowsJ2 121 122 37 39 ≤ 14219936145712 := by decide +kernel

theorem rows22250R_3747 : rowsJ2 121 122 39 41 ≤ 10614580780288 := by decide +kernel

theorem rows22250R_3748 : rowsJ2 121 122 41 44 ≤ 8564504576816 := by decide +kernel

theorem rows22250R_3749 : rowsJ2 121 122 44 49 ≤ 3189353504278 := by decide +kernel

theorem rows22250R_3750 : rowsJ2 121 122 49 61 ≤ 178982255502 := by decide +kernel

theorem rows22250R_3751 : rowsJ2 121 122 61 66 ≤ 3173367807197 := by decide +kernel

theorem rows22250R_3752 : rowsJ2 121 122 66 69 ≤ 3386167152484 := by decide +kernel

theorem rows22250R_3753 : rowsJ2 121 122 69 71 ≤ 2072323686366 := by decide +kernel

theorem rows22250R_3754 : rowsJ2 121 122 71 74 ≤ 1752154214131 := by decide +kernel

theorem rows22250R_3755 : rowsJ2 121 122 74 77 ≤ 0 := by decide +kernel

theorem rows22250R_3756 : rowsJ2 121 122 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_3757 : rowsJ2 121 122 80 83 ≤ 11326106014 := by decide +kernel

theorem rows22250R_3758 : rowsJ2 121 122 83 86 ≤ 0 := by decide +kernel

theorem rows22250R_3759 : rowsJ2 121 122 86 89 ≤ 675043553758 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3746
#print axioms SieveCert.rows22250R_3759
