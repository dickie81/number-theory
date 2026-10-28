/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1833–1848 of 5066

File 166 of 387: the parts `rows22240R_1833` … `rows22240R_1848` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96145 in units of a depth-4 test: row 79 columns 60–60, row 79 columns
61–61, row 79 columns 62–62, row 79 columns 63–63, row 79 columns 64–64, row 79 columns 65–65, row 79 columns 66–66,
row 79 columns 67–67, row 79 columns 68–68, row 79 columns 69–70, row 79 columns 71–72, row 79 columns 73–74, row 79
columns 75–76, row 79 columns 77–78, row 79 columns 79–339, row 80 columns 0–17), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1833 : rowsJ2 79 80 60 61 ≤ 408865274222 := by decide +kernel

theorem rows22240R_1834 : rowsJ2 79 80 61 62 ≤ 351780851603 := by decide +kernel

theorem rows22240R_1835 : rowsJ2 79 80 62 63 ≤ 295175699164 := by decide +kernel

theorem rows22240R_1836 : rowsJ2 79 80 63 64 ≤ 237000913517 := by decide +kernel

theorem rows22240R_1837 : rowsJ2 79 80 64 65 ≤ 179259610984 := by decide +kernel

theorem rows22240R_1838 : rowsJ2 79 80 65 66 ≤ 119843640911 := by decide +kernel

theorem rows22240R_1839 : rowsJ2 79 80 66 67 ≤ 60814171410 := by decide +kernel

theorem rows22240R_1840 : rowsJ2 79 80 67 68 ≤ 0 := by decide +kernel

theorem rows22240R_1841 : rowsJ2 79 80 68 69 ≤ 0 := by decide +kernel

theorem rows22240R_1842 : rowsJ2 79 80 69 71 ≤ 0 := by decide +kernel

theorem rows22240R_1843 : rowsJ2 79 80 71 73 ≤ 0 := by decide +kernel

theorem rows22240R_1844 : rowsJ2 79 80 73 75 ≤ 0 := by decide +kernel

theorem rows22240R_1845 : rowsJ2 79 80 75 77 ≤ 70441854374 := by decide +kernel

theorem rows22240R_1846 : rowsJ2 79 80 77 79 ≤ 3885909333073 := by decide +kernel

theorem rows22240R_1847 : rowsJ2 79 80 79 340 ≤ 3168554602432 := by decide +kernel

theorem rows22240R_1848 : rowsJ2 80 81 0 18 ≤ 327573079323 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1833
#print axioms SieveCert.rows22240R_1848
