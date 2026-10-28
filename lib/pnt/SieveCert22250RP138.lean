/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1577–1590 of 4715

File 138 of 351: the parts `rows22250R_1577` … `rows22250R_1590` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 99878 in units of a depth-4 test: row 75 columns 55–55, row 75 columns
56–56, row 75 columns 57–57, row 75 columns 58–58, row 75 columns 59–59, row 75 columns 60–60, row 75 columns 61–61,
row 75 columns 62–62, row 75 columns 63–63, row 75 columns 64–64, row 75 columns 65–65, row 75 columns 66–66, row 75
columns 67–67, row 75 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1577 : rowsJ2 75 76 55 56 ≤ 2435068013583 := by decide +kernel

theorem rows22250R_1578 : rowsJ2 75 76 56 57 ≤ 2202739476994 := by decide +kernel

theorem rows22250R_1579 : rowsJ2 75 76 57 58 ≤ 1972767089560 := by decide +kernel

theorem rows22250R_1580 : rowsJ2 75 76 58 59 ≤ 1799818906926 := by decide +kernel

theorem rows22250R_1581 : rowsJ2 75 76 59 60 ≤ 1628592375814 := by decide +kernel

theorem rows22250R_1582 : rowsJ2 75 76 60 61 ≤ 1452963148009 := by decide +kernel

theorem rows22250R_1583 : rowsJ2 75 76 61 62 ≤ 1278917566104 := by decide +kernel

theorem rows22250R_1584 : rowsJ2 75 76 62 63 ≤ 1100162428758 := by decide +kernel

theorem rows22250R_1585 : rowsJ2 75 76 63 64 ≤ 922851174965 := by decide +kernel

theorem rows22250R_1586 : rowsJ2 75 76 64 65 ≤ 740510837382 := by decide +kernel

theorem rows22250R_1587 : rowsJ2 75 76 65 66 ≤ 559471625490 := by decide +kernel

theorem rows22250R_1588 : rowsJ2 75 76 66 67 ≤ 373069251643 := by decide +kernel

theorem rows22250R_1589 : rowsJ2 75 76 67 68 ≤ 187820955721 := by decide +kernel

theorem rows22250R_1590 : rowsJ2 75 76 68 69 ≤ 63054314048 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1577
#print axioms SieveCert.rows22250R_1590
