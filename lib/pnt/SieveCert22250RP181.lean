/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1848–1865 of 5796

File 181 of 465: the parts `rows22250R_1848` … `rows22250R_1865` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 99232 tests: row 79 columns 69–69, row 79 columns 70–70, row 79 columns
71–71, row 79 columns 72–72, row 79 columns 73–73, row 79 columns 74–74, row 79 columns 75–75, row 79 columns 76–76,
row 79 columns 77–78, row 79 columns 79–359, row 80 columns 0–17, row 80 columns 18–19, row 80 columns 20–21, row 80
columns 22–22, row 80 columns 23–23, row 80 columns 24–24, row 80 columns 25–25, row 80 columns 26–26), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1848 : rowsJ2 79 80 69 70 ≤ 487785150119 := by decide +kernel

theorem rows22250R_1849 : rowsJ2 79 80 70 71 ≤ 393565300701 := by decide +kernel

theorem rows22250R_1850 : rowsJ2 79 80 71 72 ≤ 296721193962 := by decide +kernel

theorem rows22250R_1851 : rowsJ2 79 80 72 73 ≤ 200452712569 := by decide +kernel

theorem rows22250R_1852 : rowsJ2 79 80 73 74 ≤ 101398974271 := by decide +kernel

theorem rows22250R_1853 : rowsJ2 79 80 74 75 ≤ 51452026427 := by decide +kernel

theorem rows22250R_1854 : rowsJ2 79 80 75 76 ≤ 0 := by decide +kernel

theorem rows22250R_1855 : rowsJ2 79 80 76 77 ≤ 0 := by decide +kernel

theorem rows22250R_1856 : rowsJ2 79 80 77 79 ≤ 0 := by decide +kernel

theorem rows22250R_1857 : rowsJ2 79 80 79 360 ≤ 0 := by decide +kernel

theorem rows22250R_1858 : rowsJ2 80 81 0 18 ≤ 253347820618 := by decide +kernel

theorem rows22250R_1859 : rowsJ2 80 81 18 20 ≤ 712895447 := by decide +kernel

theorem rows22250R_1860 : rowsJ2 80 81 20 22 ≤ 7082847220 := by decide +kernel

theorem rows22250R_1861 : rowsJ2 80 81 22 23 ≤ 3539181000 := by decide +kernel

theorem rows22250R_1862 : rowsJ2 80 81 23 24 ≤ 2838077934 := by decide +kernel

theorem rows22250R_1863 : rowsJ2 80 81 24 25 ≤ 2125836737 := by decide +kernel

theorem rows22250R_1864 : rowsJ2 80 81 25 26 ≤ 1422999860 := by decide +kernel

theorem rows22250R_1865 : rowsJ2 80 81 26 27 ≤ 707408304 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1848
#print axioms SieveCert.rows22250R_1865
