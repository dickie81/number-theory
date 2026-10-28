/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1917–1930 of 5066

File 172 of 387: the parts `rows22240R_1917` … `rows22240R_1930` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 94513 in units of a depth-4 test: row 81 columns 53–53, row 81 columns
54–54, row 81 columns 55–55, row 81 columns 56–56, row 81 columns 57–57, row 81 columns 58–58, row 81 columns 59–59,
row 81 columns 60–60, row 81 columns 61–61, row 81 columns 62–62, row 81 columns 63–63, row 81 columns 64–64, row 81
columns 65–65, row 81 columns 66–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1917 : rowsJ2 81 82 53 54 ≤ 683982202093 := by decide +kernel

theorem rows22240R_1918 : rowsJ2 81 82 54 55 ≤ 572799341926 := by decide +kernel

theorem rows22240R_1919 : rowsJ2 81 82 55 56 ≤ 458870087479 := by decide +kernel

theorem rows22240R_1920 : rowsJ2 81 82 56 57 ≤ 345987065848 := by decide +kernel

theorem rows22240R_1921 : rowsJ2 81 82 57 58 ≤ 230161185157 := by decide +kernel

theorem rows22240R_1922 : rowsJ2 81 82 58 59 ≤ 115285056334 := by decide +kernel

theorem rows22240R_1923 : rowsJ2 81 82 59 60 ≤ 57424496303 := by decide +kernel

theorem rows22240R_1924 : rowsJ2 81 82 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_1925 : rowsJ2 81 82 61 62 ≤ 0 := by decide +kernel

theorem rows22240R_1926 : rowsJ2 81 82 62 63 ≤ 0 := by decide +kernel

theorem rows22240R_1927 : rowsJ2 81 82 63 64 ≤ 0 := by decide +kernel

theorem rows22240R_1928 : rowsJ2 81 82 64 65 ≤ 0 := by decide +kernel

theorem rows22240R_1929 : rowsJ2 81 82 65 66 ≤ 0 := by decide +kernel

theorem rows22240R_1930 : rowsJ2 81 82 66 67 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1917
#print axioms SieveCert.rows22240R_1930
