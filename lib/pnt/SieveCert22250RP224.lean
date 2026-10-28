/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2802–2818 of 4715

File 224 of 351: the parts `rows22250R_2802` … `rows22250R_2818` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 99136 in units of a depth-4 test: row 104 columns 97–97, row 104
columns 98–98, row 104 columns 99–99, row 104 columns 100–100, row 104 columns 101–101, row 104 columns 102–339, row
105 columns 0–23, row 105 columns 24–30, row 105 columns 31–33, row 105 columns 34–35, row 105 columns 36–36, row
105 columns 37–37, row 105 columns 38–38, row 105 columns 39–39, row 105 columns 40–41, row 105 columns 42–43, row
105 columns 44–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at
a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2802 : rowsJ2 104 105 97 98 ≤ 7876734935913 := by decide +kernel

theorem rows22250R_2803 : rowsJ2 104 105 98 99 ≤ 9028880069968 := by decide +kernel

theorem rows22250R_2804 : rowsJ2 104 105 99 100 ≤ 10300228245528 := by decide +kernel

theorem rows22250R_2805 : rowsJ2 104 105 100 101 ≤ 11641678982442 := by decide +kernel

theorem rows22250R_2806 : rowsJ2 104 105 101 102 ≤ 13109589947864 := by decide +kernel

theorem rows22250R_2807 : rowsJ2 104 105 102 340 ≤ 277730759792642 := by decide +kernel

theorem rows22250R_2808 : rowsJ2 105 106 0 24 ≤ 0 := by decide +kernel

theorem rows22250R_2809 : rowsJ2 105 106 24 31 ≤ 4968369924362 := by decide +kernel

theorem rows22250R_2810 : rowsJ2 105 106 31 34 ≤ 15828401625489 := by decide +kernel

theorem rows22250R_2811 : rowsJ2 105 106 34 36 ≤ 19493066980805 := by decide +kernel

theorem rows22250R_2812 : rowsJ2 105 106 36 37 ≤ 13081504587670 := by decide +kernel

theorem rows22250R_2813 : rowsJ2 105 106 37 38 ≤ 15817228129705 := by decide +kernel

theorem rows22250R_2814 : rowsJ2 105 106 38 39 ≤ 13690062393312 := by decide +kernel

theorem rows22250R_2815 : rowsJ2 105 106 39 40 ≤ 11655312005393 := by decide +kernel

theorem rows22250R_2816 : rowsJ2 105 106 40 42 ≤ 18038677287277 := by decide +kernel

theorem rows22250R_2817 : rowsJ2 105 106 42 44 ≤ 12348280568522 := by decide +kernel

theorem rows22250R_2818 : rowsJ2 105 106 44 46 ≤ 7794495045261 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2802
#print axioms SieveCert.rows22250R_2818
