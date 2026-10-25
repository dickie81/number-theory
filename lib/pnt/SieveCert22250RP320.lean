/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3760–3775 of 5796

File 320 of 465: the parts `rows22250R_3760` … `rows22250R_3775` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97185 tests: row 121 columns 89–91, row 121 columns 92–93, row 121 columns
94–95, row 121 columns 96–97, row 121 columns 98–98, row 121 columns 99–99, row 121 columns 100–100, row 121 columns
101–101, row 121 columns 102–102, row 121 columns 103–359, row 122 columns 0–27, row 122 columns 28–30, row 122
columns 31–32, row 122 columns 33–34, row 122 columns 35–36, row 122 columns 37–38), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3760 : rowsJ2 121 122 89 92 ≤ 3674447530952 := by decide +kernel

theorem rows22250R_3761 : rowsJ2 121 122 92 94 ≤ 5008594892382 := by decide +kernel

theorem rows22250R_3762 : rowsJ2 121 122 94 96 ≤ 7711401349818 := by decide +kernel

theorem rows22250R_3763 : rowsJ2 121 122 96 98 ≤ 11014589662005 := by decide +kernel

theorem rows22250R_3764 : rowsJ2 121 122 98 99 ≤ 6949203209409 := by decide +kernel

theorem rows22250R_3765 : rowsJ2 121 122 99 100 ≤ 8006411734763 := by decide +kernel

theorem rows22250R_3766 : rowsJ2 121 122 100 101 ≤ 9172234658443 := by decide +kernel

theorem rows22250R_3767 : rowsJ2 121 122 101 102 ≤ 10405202551579 := by decide +kernel

theorem rows22250R_3768 : rowsJ2 121 122 102 103 ≤ 11753706790568 := by decide +kernel

theorem rows22250R_3769 : rowsJ2 121 122 103 360 ≤ 1404227348327717 := by decide +kernel

theorem rows22250R_3770 : rowsJ2 122 123 0 28 ≤ 950450515309 := by decide +kernel

theorem rows22250R_3771 : rowsJ2 122 123 28 31 ≤ 6318227829024 := by decide +kernel

theorem rows22250R_3772 : rowsJ2 122 123 31 33 ≤ 10194997424902 := by decide +kernel

theorem rows22250R_3773 : rowsJ2 122 123 33 35 ≤ 16562685470206 := by decide +kernel

theorem rows22250R_3774 : rowsJ2 122 123 35 37 ≤ 15949178735662 := by decide +kernel

theorem rows22250R_3775 : rowsJ2 122 123 37 39 ≤ 12706449508350 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3760
#print axioms SieveCert.rows22250R_3775
