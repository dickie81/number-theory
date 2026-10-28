/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1875–1889 of 5066

File 169 of 387: the parts `rows22240R_1875` … `rows22240R_1889` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 96473 in units of a depth-4 test: row 80 columns 56–56, row 80 columns
57–57, row 80 columns 58–58, row 80 columns 59–59, row 80 columns 60–60, row 80 columns 61–61, row 80 columns 62–62,
row 80 columns 63–63, row 80 columns 64–64, row 80 columns 65–65, row 80 columns 66–66, row 80 columns 67–67, row 80
columns 68–69, row 80 columns 70–71, row 80 columns 72–73), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1875 : rowsJ2 80 81 56 57 ≤ 633574789655 := by decide +kernel

theorem rows22240R_1876 : rowsJ2 80 81 57 58 ≤ 461513295805 := by decide +kernel

theorem rows22240R_1877 : rowsJ2 80 81 58 59 ≤ 346086872774 := by decide +kernel

theorem rows22240R_1878 : rowsJ2 80 81 59 60 ≤ 231612128853 := by decide +kernel

theorem rows22240R_1879 : rowsJ2 80 81 60 61 ≤ 174068809091 := by decide +kernel

theorem rows22240R_1880 : rowsJ2 80 81 61 62 ≤ 116976309334 := by decide +kernel

theorem rows22240R_1881 : rowsJ2 80 81 62 63 ≤ 117245073685 := by decide +kernel

theorem rows22240R_1882 : rowsJ2 80 81 63 64 ≤ 59115249492 := by decide +kernel

theorem rows22240R_1883 : rowsJ2 80 81 64 65 ≤ 59273077637 := by decide +kernel

theorem rows22240R_1884 : rowsJ2 80 81 65 66 ≤ 0 := by decide +kernel

theorem rows22240R_1885 : rowsJ2 80 81 66 67 ≤ 0 := by decide +kernel

theorem rows22240R_1886 : rowsJ2 80 81 67 68 ≤ 0 := by decide +kernel

theorem rows22240R_1887 : rowsJ2 80 81 68 70 ≤ 0 := by decide +kernel

theorem rows22240R_1888 : rowsJ2 80 81 70 72 ≤ 0 := by decide +kernel

theorem rows22240R_1889 : rowsJ2 80 81 72 74 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1875
#print axioms SieveCert.rows22240R_1889
