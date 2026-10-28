/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1865–1874 of 5066

File 168 of 387: the parts `rows22240R_1865` … `rows22240R_1874` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (10 parts, work 93336 in units of a depth-4 test: row 80 columns 46–46, row 80 columns
47–47, row 80 columns 48–48, row 80 columns 49–49, row 80 columns 50–50, row 80 columns 51–51, row 80 columns 52–52,
row 80 columns 53–53, row 80 columns 54–54, row 80 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1865 : rowsJ2 80 81 46 47 ≤ 335990489749 := by decide +kernel

theorem rows22240R_1866 : rowsJ2 80 81 47 48 ≤ 665648394176 := by decide +kernel

theorem rows22240R_1867 : rowsJ2 80 81 48 49 ≤ 1062277538147 := by decide +kernel

theorem rows22240R_1868 : rowsJ2 80 81 49 50 ≤ 1294786174967 := by decide +kernel

theorem rows22240R_1869 : rowsJ2 80 81 50 51 ≤ 1355401522625 := by decide +kernel

theorem rows22240R_1870 : rowsJ2 80 81 51 52 ≤ 1305822834752 := by decide +kernel

theorem rows22240R_1871 : rowsJ2 80 81 52 53 ≤ 1195356853192 := by decide +kernel

theorem rows22240R_1872 : rowsJ2 80 81 53 54 ≤ 1028209621505 := by decide +kernel

theorem rows22240R_1873 : rowsJ2 80 81 54 55 ≤ 916422726168 := by decide +kernel

theorem rows22240R_1874 : rowsJ2 80 81 55 56 ≤ 747012822514 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1865
#print axioms SieveCert.rows22240R_1874
