/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1755–1770 of 4715

File 151 of 351: the parts `rows22250R_1755` … `rows22250R_1770` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99375 tests: row 79 columns 62–62, row 79 columns 63–63, row 79 columns
64–64, row 79 columns 65–65, row 79 columns 66–67, row 79 columns 68–69, row 79 columns 70–71, row 79 columns 72–74,
row 79 columns 75–77, row 79 columns 78–339, row 80 columns 0–16, row 80 columns 17–18, row 80 columns 19–20, row 80
columns 21–22, row 80 columns 23–24, row 80 columns 25–27), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1755 : rowsJ2 79 80 62 63 ≤ 121383546638 := by decide +kernel

theorem rows22250R_1756 : rowsJ2 79 80 63 64 ≤ 61575760657 := by decide +kernel

theorem rows22250R_1757 : rowsJ2 79 80 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_1758 : rowsJ2 79 80 65 66 ≤ 0 := by decide +kernel

theorem rows22250R_1759 : rowsJ2 79 80 66 68 ≤ 0 := by decide +kernel

theorem rows22250R_1760 : rowsJ2 79 80 68 70 ≤ 0 := by decide +kernel

theorem rows22250R_1761 : rowsJ2 79 80 70 72 ≤ 0 := by decide +kernel

theorem rows22250R_1762 : rowsJ2 79 80 72 75 ≤ 0 := by decide +kernel

theorem rows22250R_1763 : rowsJ2 79 80 75 78 ≤ 413969257352 := by decide +kernel

theorem rows22250R_1764 : rowsJ2 79 80 78 340 ≤ 2995463342472 := by decide +kernel

theorem rows22250R_1765 : rowsJ2 80 81 0 17 ≤ 88917237594 := by decide +kernel

theorem rows22250R_1766 : rowsJ2 80 81 17 19 ≤ 11220612395 := by decide +kernel

theorem rows22250R_1767 : rowsJ2 80 81 19 21 ≤ 6173080358 := by decide +kernel

theorem rows22250R_1768 : rowsJ2 80 81 21 23 ≤ 0 := by decide +kernel

theorem rows22250R_1769 : rowsJ2 80 81 23 25 ≤ 0 := by decide +kernel

theorem rows22250R_1770 : rowsJ2 80 81 25 28 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1755
#print axioms SieveCert.rows22250R_1770
