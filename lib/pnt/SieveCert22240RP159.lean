/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1737–1751 of 5066

File 159 of 387: the parts `rows22240R_1737` … `rows22240R_1751` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 97006 in units of a depth-4 test: row 77 columns 59–59, row 77 columns
60–60, row 77 columns 61–61, row 77 columns 62–62, row 77 columns 63–63, row 77 columns 64–64, row 77 columns 65–65,
row 77 columns 66–66, row 77 columns 67–67, row 77 columns 68–68, row 77 columns 69–69, row 77 columns 70–70, row 77
columns 71–72, row 77 columns 73–74, row 77 columns 75–76), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_1737 : rowsJ2 77 78 59 60 ≤ 1287587048271 := by decide +kernel

theorem rows22240R_1738 : rowsJ2 77 78 60 61 ≤ 1117559967607 := by decide +kernel

theorem rows22240R_1739 : rowsJ2 77 78 61 62 ≤ 1003971410050 := by decide +kernel

theorem rows22240R_1740 : rowsJ2 77 78 62 63 ≤ 891410686739 := by decide +kernel

theorem rows22240R_1741 : rowsJ2 77 78 63 64 ≤ 775808506550 := by decide +kernel

theorem rows22240R_1742 : rowsJ2 77 78 64 65 ≤ 661144676138 := by decide +kernel

theorem rows22240R_1743 : rowsJ2 77 78 65 66 ≤ 543233535874 := by decide +kernel

theorem rows22240R_1744 : rowsJ2 77 78 66 67 ≤ 426169346292 := by decide +kernel

theorem rows22240R_1745 : rowsJ2 77 78 67 68 ≤ 305642629433 := by decide +kernel

theorem rows22240R_1746 : rowsJ2 77 78 68 69 ≤ 185868725625 := by decide +kernel

theorem rows22240R_1747 : rowsJ2 77 78 69 70 ≤ 62406433145 := by decide +kernel

theorem rows22240R_1748 : rowsJ2 77 78 70 71 ≤ 0 := by decide +kernel

theorem rows22240R_1749 : rowsJ2 77 78 71 73 ≤ 0 := by decide +kernel

theorem rows22240R_1750 : rowsJ2 77 78 73 75 ≤ 0 := by decide +kernel

theorem rows22240R_1751 : rowsJ2 77 78 75 77 ≤ 71761816546 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1737
#print axioms SieveCert.rows22240R_1751
