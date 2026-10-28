/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3752–3764 of 4715

File 288 of 351: the parts `rows22250R_3752` … `rows22250R_3764` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 90489 in units of a depth-4 test: row 140 columns 77–82, row 140
columns 83–339, row 141 columns 0–25, row 141 columns 26–48, row 141 columns 49–51, row 141 columns 52–53, row 141
columns 54–54, row 141 columns 55–55, row 141 columns 56–56, row 141 columns 57–57, row 141 columns 58–58, row 141
columns 59–59, row 141 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_3752 : rowsJ2 140 141 77 83 ≤ 3492571683224 := by decide +kernel

theorem rows22250R_3753 : rowsJ2 140 141 83 340 ≤ 925427711971330 := by decide +kernel

theorem rows22250R_3754 : rowsJ2 141 142 0 26 ≤ 2899316252887 := by decide +kernel

theorem rows22250R_3755 : rowsJ2 141 142 26 49 ≤ 5526215534390 := by decide +kernel

theorem rows22250R_3756 : rowsJ2 141 142 49 52 ≤ 9112119796148 := by decide +kernel

theorem rows22250R_3757 : rowsJ2 141 142 52 54 ≤ 9489625231035 := by decide +kernel

theorem rows22250R_3758 : rowsJ2 141 142 54 55 ≤ 5918931239711 := by decide +kernel

theorem rows22250R_3759 : rowsJ2 141 142 55 56 ≤ 6763319263207 := by decide +kernel

theorem rows22250R_3760 : rowsJ2 141 142 56 57 ≤ 7651644981895 := by decide +kernel

theorem rows22250R_3761 : rowsJ2 141 142 57 58 ≤ 8582246816372 := by decide +kernel

theorem rows22250R_3762 : rowsJ2 141 142 58 59 ≤ 9553598948460 := by decide +kernel

theorem rows22250R_3763 : rowsJ2 141 142 59 60 ≤ 10564304427419 := by decide +kernel

theorem rows22250R_3764 : rowsJ2 141 142 60 61 ≤ 11592555626778 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3752
#print axioms SieveCert.rows22250R_3764
