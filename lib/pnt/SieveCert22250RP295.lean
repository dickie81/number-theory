/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3846–3861 of 4715

File 295 of 351: the parts `rows22250R_3846` … `rows22250R_3861` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98755 tests: row 144 columns 65–65, row 144 columns 66–66, row 144 columns
67–67, row 144 columns 68–68, row 144 columns 69–70, row 144 columns 71–72, row 144 columns 73–76, row 144 columns
77–339, row 145 columns 0–43, row 145 columns 44–47, row 145 columns 48–49, row 145 columns 50–51, row 145 columns
52–52, row 145 columns 53–53, row 145 columns 54–54, row 145 columns 55–55), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3846 : rowsJ2 144 145 65 66 ≤ 7746745367469 := by decide +kernel

theorem rows22250R_3847 : rowsJ2 144 145 66 67 ≤ 6750489190026 := by decide +kernel

theorem rows22250R_3848 : rowsJ2 144 145 67 68 ≤ 5827883381863 := by decide +kernel

theorem rows22250R_3849 : rowsJ2 144 145 68 69 ≤ 4977401426978 := by decide +kernel

theorem rows22250R_3850 : rowsJ2 144 145 69 71 ≤ 7684958810916 := by decide +kernel

theorem rows22250R_3851 : rowsJ2 144 145 71 73 ≤ 5115697223110 := by decide +kernel

theorem rows22250R_3852 : rowsJ2 144 145 73 77 ≤ 4646819468797 := by decide +kernel

theorem rows22250R_3853 : rowsJ2 144 145 77 340 ≤ 1328145065351362 := by decide +kernel

theorem rows22250R_3854 : rowsJ2 145 146 0 44 ≤ 1965182512959 := by decide +kernel

theorem rows22250R_3855 : rowsJ2 145 146 44 48 ≤ 7188774376654 := by decide +kernel

theorem rows22250R_3856 : rowsJ2 145 146 48 50 ≤ 7148592375966 := by decide +kernel

theorem rows22250R_3857 : rowsJ2 145 146 50 52 ≤ 10138163628129 := by decide +kernel

theorem rows22250R_3858 : rowsJ2 145 146 52 53 ≤ 6320926045570 := by decide +kernel

theorem rows22250R_3859 : rowsJ2 145 146 53 54 ≤ 7220812650614 := by decide +kernel

theorem rows22250R_3860 : rowsJ2 145 146 54 55 ≤ 8167236253311 := by decide +kernel

theorem rows22250R_3861 : rowsJ2 145 146 55 56 ≤ 9158423752990 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3846
#print axioms SieveCert.rows22250R_3861
