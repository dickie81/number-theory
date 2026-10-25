/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3670–3686 of 5796

File 314 of 465: the parts `rows22250R_3670` … `rows22250R_3686` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 96871 tests: row 118 columns 89–91, row 118 columns 92–93, row 118 columns
94–95, row 118 columns 96–97, row 118 columns 98–98, row 118 columns 99–99, row 118 columns 100–100, row 118 columns
101–101, row 118 columns 102–102, row 118 columns 103–103, row 118 columns 104–359, row 119 columns 0–27, row 119
columns 28–31, row 119 columns 32–33, row 119 columns 34–34, row 119 columns 35–35, row 119 columns 36–36), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3670 : rowsJ2 118 119 89 92 ≤ 2848158577700 := by decide +kernel

theorem rows22250R_3671 : rowsJ2 118 119 92 94 ≤ 4025920700222 := by decide +kernel

theorem rows22250R_3672 : rowsJ2 118 119 94 96 ≤ 6342638403186 := by decide +kernel

theorem rows22250R_3673 : rowsJ2 118 119 96 98 ≤ 9215295258697 := by decide +kernel

theorem rows22250R_3674 : rowsJ2 118 119 98 99 ≤ 5861978772820 := by decide +kernel

theorem rows22250R_3675 : rowsJ2 118 119 99 100 ≤ 6813963678216 := by decide +kernel

theorem rows22250R_3676 : rowsJ2 118 119 100 101 ≤ 7823944598344 := by decide +kernel

theorem rows22250R_3677 : rowsJ2 118 119 101 102 ≤ 8937353894032 := by decide +kernel

theorem rows22250R_3678 : rowsJ2 118 119 102 103 ≤ 10113648567454 := by decide +kernel

theorem rows22250R_3679 : rowsJ2 118 119 103 104 ≤ 11399706406666 := by decide +kernel

theorem rows22250R_3680 : rowsJ2 118 119 104 360 ≤ 1310476721036915 := by decide +kernel

theorem rows22250R_3681 : rowsJ2 119 120 0 28 ≤ 185158817999 := by decide +kernel

theorem rows22250R_3682 : rowsJ2 119 120 28 32 ≤ 7977520661854 := by decide +kernel

theorem rows22250R_3683 : rowsJ2 119 120 32 34 ≤ 10903955880915 := by decide +kernel

theorem rows22250R_3684 : rowsJ2 119 120 34 35 ≤ 7645910970917 := by decide +kernel

theorem rows22250R_3685 : rowsJ2 119 120 35 36 ≤ 9417848242960 := by decide +kernel

theorem rows22250R_3686 : rowsJ2 119 120 36 37 ≤ 9978896894784 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3670
#print axioms SieveCert.rows22250R_3686
