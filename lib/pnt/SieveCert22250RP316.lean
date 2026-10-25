/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3701–3716 of 5796

File 316 of 465: the parts `rows22250R_3701` … `rows22250R_3716` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 92886 tests: row 119 columns 89–91, row 119 columns 92–93, row 119 columns
94–95, row 119 columns 96–97, row 119 columns 98–98, row 119 columns 99–99, row 119 columns 100–100, row 119 columns
101–101, row 119 columns 102–102, row 119 columns 103–103, row 119 columns 104–359, row 120 columns 0–27, row 120
columns 28–31, row 120 columns 32–33, row 120 columns 34–34, row 120 columns 35–35), each a sum of refined costs
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

theorem rows22250R_3701 : rowsJ2 119 120 89 92 ≤ 3090385249025 := by decide +kernel

theorem rows22250R_3702 : rowsJ2 119 120 92 94 ≤ 4331115733442 := by decide +kernel

theorem rows22250R_3703 : rowsJ2 119 120 94 96 ≤ 6772312695740 := by decide +kernel

theorem rows22250R_3704 : rowsJ2 119 120 96 98 ≤ 9783585497564 := by decide +kernel

theorem rows22250R_3705 : rowsJ2 119 120 98 99 ≤ 6213620947672 := by decide +kernel

theorem rows22250R_3706 : rowsJ2 119 120 99 100 ≤ 7185060205883 := by decide +kernel

theorem rows22250R_3707 : rowsJ2 119 120 100 101 ≤ 8259611805205 := by decide +kernel

theorem rows22250R_3708 : rowsJ2 119 120 101 102 ≤ 9396661147496 := by decide +kernel

theorem rows22250R_3709 : rowsJ2 119 120 102 103 ≤ 10643075093530 := by decide +kernel

theorem rows22250R_3710 : rowsJ2 119 120 103 104 ≤ 11957538626287 := by decide +kernel

theorem rows22250R_3711 : rowsJ2 119 120 104 360 ≤ 1376625212523334 := by decide +kernel

theorem rows22250R_3712 : rowsJ2 120 121 0 28 ≤ 374288949896 := by decide +kernel

theorem rows22250R_3713 : rowsJ2 120 121 28 32 ≤ 8889721353144 := by decide +kernel

theorem rows22250R_3714 : rowsJ2 120 121 32 34 ≤ 11606890777625 := by decide +kernel

theorem rows22250R_3715 : rowsJ2 120 121 34 35 ≤ 8079947150951 := by decide +kernel

theorem rows22250R_3716 : rowsJ2 120 121 35 36 ≤ 10037112301213 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3701
#print axioms SieveCert.rows22250R_3716
