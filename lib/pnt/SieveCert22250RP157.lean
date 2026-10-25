/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1843–1857 of 4715

File 157 of 351: the parts `rows22250R_1843` … `rows22250R_1857` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94415 tests: row 81 columns 68–69, row 81 columns 70–72, row 81 columns
73–75, row 81 columns 76–77, row 81 columns 78–79, row 81 columns 80–80, row 81 columns 81–339, row 82 columns 0–16,
row 82 columns 17–19, row 82 columns 20–21, row 82 columns 22–23, row 82 columns 24–26, row 82 columns 27–30, row 82
columns 31–34, row 82 columns 35–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1843 : rowsJ2 81 82 68 70 ≤ 0 := by decide +kernel

theorem rows22250R_1844 : rowsJ2 81 82 70 73 ≤ 0 := by decide +kernel

theorem rows22250R_1845 : rowsJ2 81 82 73 76 ≤ 17845595576 := by decide +kernel

theorem rows22250R_1846 : rowsJ2 81 82 76 78 ≤ 389657016189 := by decide +kernel

theorem rows22250R_1847 : rowsJ2 81 82 78 80 ≤ 2325903200726 := by decide +kernel

theorem rows22250R_1848 : rowsJ2 81 82 80 81 ≤ 1740959951039 := by decide +kernel

theorem rows22250R_1849 : rowsJ2 81 82 81 340 ≤ 2112108644339 := by decide +kernel

theorem rows22250R_1850 : rowsJ2 82 83 0 17 ≤ 39983969546 := by decide +kernel

theorem rows22250R_1851 : rowsJ2 82 83 17 20 ≤ 6266252543 := by decide +kernel

theorem rows22250R_1852 : rowsJ2 82 83 20 22 ≤ 0 := by decide +kernel

theorem rows22250R_1853 : rowsJ2 82 83 22 24 ≤ 0 := by decide +kernel

theorem rows22250R_1854 : rowsJ2 82 83 24 27 ≤ 0 := by decide +kernel

theorem rows22250R_1855 : rowsJ2 82 83 27 31 ≤ 0 := by decide +kernel

theorem rows22250R_1856 : rowsJ2 82 83 31 35 ≤ 963770953909 := by decide +kernel

theorem rows22250R_1857 : rowsJ2 82 83 35 38 ≤ 7101884967753 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1843
#print axioms SieveCert.rows22250R_1857
