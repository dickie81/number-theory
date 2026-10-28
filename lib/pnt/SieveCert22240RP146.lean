/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1562–1577 of 5066

File 146 of 387: the parts `rows22240R_1562` … `rows22240R_1577` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94919 in units of a depth-4 test: row 74 columns 28–28, row 74 columns
29–29, row 74 columns 30–30, row 74 columns 31–32, row 74 columns 33–34, row 74 columns 35–36, row 74 columns 37–38,
row 74 columns 39–40, row 74 columns 41–41, row 74 columns 42–42, row 74 columns 43–43, row 74 columns 44–44, row 74
columns 45–45, row 74 columns 46–46, row 74 columns 47–47, row 74 columns 48–48), each a sum of refined costs
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

theorem rows22240R_1562 : rowsJ2 74 75 28 29 ≤ 2878171035 := by decide +kernel

theorem rows22240R_1563 : rowsJ2 74 75 29 30 ≤ 1928574761 := by decide +kernel

theorem rows22240R_1564 : rowsJ2 74 75 30 31 ≤ 959241866 := by decide +kernel

theorem rows22240R_1565 : rowsJ2 74 75 31 33 ≤ 0 := by decide +kernel

theorem rows22240R_1566 : rowsJ2 74 75 33 35 ≤ 0 := by decide +kernel

theorem rows22240R_1567 : rowsJ2 74 75 35 37 ≤ 0 := by decide +kernel

theorem rows22240R_1568 : rowsJ2 74 75 37 39 ≤ 0 := by decide +kernel

theorem rows22240R_1569 : rowsJ2 74 75 39 41 ≤ 0 := by decide +kernel

theorem rows22240R_1570 : rowsJ2 74 75 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1571 : rowsJ2 74 75 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1572 : rowsJ2 74 75 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1573 : rowsJ2 74 75 44 45 ≤ 61844014833 := by decide +kernel

theorem rows22240R_1574 : rowsJ2 74 75 45 46 ≤ 180859241512 := by decide +kernel

theorem rows22240R_1575 : rowsJ2 74 75 46 47 ≤ 352700865771 := by decide +kernel

theorem rows22240R_1576 : rowsJ2 74 75 47 48 ≤ 753045685154 := by decide +kernel

theorem rows22240R_1577 : rowsJ2 74 75 48 49 ≤ 1438693596606 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1562
#print axioms SieveCert.rows22240R_1577
