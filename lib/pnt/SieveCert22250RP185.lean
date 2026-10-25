/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1899–1915 of 5796

File 185 of 465: the parts `rows22250R_1899` … `rows22250R_1915` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 96083 tests: row 80 columns 68–68, row 80 columns 69–69, row 80 columns
70–70, row 80 columns 71–71, row 80 columns 72–72, row 80 columns 73–73, row 80 columns 74–74, row 80 columns 75–75,
row 80 columns 76–77, row 80 columns 78–79, row 80 columns 80–359, row 81 columns 0–17, row 81 columns 18–19, row 81
columns 20–21, row 81 columns 22–22, row 81 columns 23–23, row 81 columns 24–24), each a sum of refined costs
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

theorem rows22250R_1899 : rowsJ2 80 81 68 69 ≤ 337718179761 := by decide +kernel

theorem rows22250R_1900 : rowsJ2 80 81 69 70 ≤ 243007849681 := by decide +kernel

theorem rows22250R_1901 : rowsJ2 80 81 70 71 ≤ 195491270729 := by decide +kernel

theorem rows22250R_1902 : rowsJ2 80 81 71 72 ≤ 98853866801 := by decide +kernel

theorem rows22250R_1903 : rowsJ2 80 81 72 73 ≤ 50140939100 := by decide +kernel

theorem rows22250R_1904 : rowsJ2 80 81 73 74 ≤ 0 := by decide +kernel

theorem rows22250R_1905 : rowsJ2 80 81 74 75 ≤ 0 := by decide +kernel

theorem rows22250R_1906 : rowsJ2 80 81 75 76 ≤ 0 := by decide +kernel

theorem rows22250R_1907 : rowsJ2 80 81 76 78 ≤ 0 := by decide +kernel

theorem rows22250R_1908 : rowsJ2 80 81 78 80 ≤ 0 := by decide +kernel

theorem rows22250R_1909 : rowsJ2 80 81 80 360 ≤ 59275780916 := by decide +kernel

theorem rows22250R_1910 : rowsJ2 81 82 0 18 ≤ 201622464439 := by decide +kernel

theorem rows22250R_1911 : rowsJ2 81 82 18 20 ≤ 1425324732 := by decide +kernel

theorem rows22250R_1912 : rowsJ2 81 82 20 22 ≤ 10620863043 := by decide +kernel

theorem rows22250R_1913 : rowsJ2 81 82 22 23 ≤ 4950456014 := by decide +kernel

theorem rows22250R_1914 : rowsJ2 81 82 23 24 ≤ 3536366624 := by decide +kernel

theorem rows22250R_1915 : rowsJ2 81 82 24 25 ≤ 2830608649 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1899
#print axioms SieveCert.rows22250R_1915
