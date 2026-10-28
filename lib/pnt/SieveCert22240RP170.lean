/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1890–1904 of 5066

File 170 of 387: the parts `rows22240R_1890` … `rows22240R_1904` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98904 in units of a depth-4 test: row 80 columns 74–75, row 80 columns
76–77, row 80 columns 78–79, row 80 columns 80–339, row 81 columns 0–17, row 81 columns 18–19, row 81 columns 20–21,
row 81 columns 22–23, row 81 columns 24–25, row 81 columns 26–27, row 81 columns 28–29, row 81 columns 30–32, row 81
columns 33–35, row 81 columns 36–38, row 81 columns 39–40), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_1890 : rowsJ2 80 81 74 76 ≤ 0 := by decide +kernel

theorem rows22240R_1891 : rowsJ2 80 81 76 78 ≤ 1430410306666 := by decide +kernel

theorem rows22240R_1892 : rowsJ2 80 81 78 80 ≤ 5117992339211 := by decide +kernel

theorem rows22240R_1893 : rowsJ2 80 81 80 340 ≤ 3174576663379 := by decide +kernel

theorem rows22240R_1894 : rowsJ2 81 82 0 18 ≤ 261993301023 := by decide +kernel

theorem rows22240R_1895 : rowsJ2 81 82 18 20 ≤ 17685888724 := by decide +kernel

theorem rows22240R_1896 : rowsJ2 81 82 20 22 ≤ 15897795002 := by decide +kernel

theorem rows22240R_1897 : rowsJ2 81 82 22 24 ≤ 5649331821 := by decide +kernel

theorem rows22240R_1898 : rowsJ2 81 82 24 26 ≤ 0 := by decide +kernel

theorem rows22240R_1899 : rowsJ2 81 82 26 28 ≤ 0 := by decide +kernel

theorem rows22240R_1900 : rowsJ2 81 82 28 30 ≤ 0 := by decide +kernel

theorem rows22240R_1901 : rowsJ2 81 82 30 33 ≤ 0 := by decide +kernel

theorem rows22240R_1902 : rowsJ2 81 82 33 36 ≤ 1230145289943 := by decide +kernel

theorem rows22240R_1903 : rowsJ2 81 82 36 39 ≤ 6536391213686 := by decide +kernel

theorem rows22240R_1904 : rowsJ2 81 82 39 41 ≤ 5762845491258 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1890
#print axioms SieveCert.rows22240R_1904
