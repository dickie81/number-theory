/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1914–1929 of 4715

File 162 of 351: the parts `rows22250R_1914` … `rows22250R_1929` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 97438 in units of a depth-4 test: row 83 columns 54–54, row 83 columns
55–55, row 83 columns 56–56, row 83 columns 57–57, row 83 columns 58–58, row 83 columns 59–59, row 83 columns 60–60,
row 83 columns 61–61, row 83 columns 62–63, row 83 columns 64–65, row 83 columns 66–67, row 83 columns 68–70, row 83
columns 71–74, row 83 columns 75–77, row 83 columns 78–79, row 83 columns 80–80), each a sum of refined costs
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

theorem rows22250R_1914 : rowsJ2 83 84 54 55 ≤ 58505632551 := by decide +kernel

theorem rows22250R_1915 : rowsJ2 83 84 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_1916 : rowsJ2 83 84 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_1917 : rowsJ2 83 84 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_1918 : rowsJ2 83 84 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_1919 : rowsJ2 83 84 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_1920 : rowsJ2 83 84 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_1921 : rowsJ2 83 84 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_1922 : rowsJ2 83 84 62 64 ≤ 0 := by decide +kernel

theorem rows22250R_1923 : rowsJ2 83 84 64 66 ≤ 0 := by decide +kernel

theorem rows22250R_1924 : rowsJ2 83 84 66 68 ≤ 0 := by decide +kernel

theorem rows22250R_1925 : rowsJ2 83 84 68 71 ≤ 0 := by decide +kernel

theorem rows22250R_1926 : rowsJ2 83 84 71 75 ≤ 0 := by decide +kernel

theorem rows22250R_1927 : rowsJ2 83 84 75 78 ≤ 401234890699 := by decide +kernel

theorem rows22250R_1928 : rowsJ2 83 84 78 80 ≤ 1736696356112 := by decide +kernel

theorem rows22250R_1929 : rowsJ2 83 84 80 81 ≤ 1365491977029 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1914
#print axioms SieveCert.rows22250R_1929
