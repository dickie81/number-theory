/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1684–1695 of 5066

File 155 of 387: the parts `rows22240R_1684` … `rows22240R_1695` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 99914 in units of a depth-4 test: row 76 columns 55–55, row 76 columns
56–56, row 76 columns 57–57, row 76 columns 58–58, row 76 columns 59–59, row 76 columns 60–60, row 76 columns 61–61,
row 76 columns 62–62, row 76 columns 63–63, row 76 columns 64–64, row 76 columns 65–65, row 76 columns 66–66), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1684 : rowsJ2 76 77 55 56 ≤ 2668077264657 := by decide +kernel

theorem rows22240R_1685 : rowsJ2 76 77 56 57 ≤ 2442152413712 := by decide +kernel

theorem rows22240R_1686 : rowsJ2 76 77 57 58 ≤ 2156984227367 := by decide +kernel

theorem rows22240R_1687 : rowsJ2 76 77 58 59 ≤ 1927836310978 := by decide +kernel

theorem rows22240R_1688 : rowsJ2 76 77 59 60 ≤ 1700876726668 := by decide +kernel

theorem rows22240R_1689 : rowsJ2 76 77 60 61 ≤ 1530059951574 := by decide +kernel

theorem rows22240R_1690 : rowsJ2 76 77 61 62 ≤ 1360828112777 := by decide +kernel

theorem rows22240R_1691 : rowsJ2 76 77 62 63 ≤ 1247993508971 := by decide +kernel

theorem rows22240R_1692 : rowsJ2 76 77 63 64 ≤ 1075888441935 := by decide +kernel

theorem rows22240R_1693 : rowsJ2 76 77 64 65 ≤ 960940751225 := by decide +kernel

theorem rows22240R_1694 : rowsJ2 76 77 65 66 ≤ 785568917291 := by decide +kernel

theorem rows22240R_1695 : rowsJ2 76 77 66 67 ≤ 668167413829 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1684
#print axioms SieveCert.rows22240R_1695
