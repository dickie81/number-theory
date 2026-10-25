/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1748–1765 of 5796

File 173 of 465: the parts `rows22250R_1748` … `rows22250R_1765` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 99399 tests: row 77 columns 75–75, row 77 columns 76–76, row 77 columns
77–359, row 78 columns 0–17, row 78 columns 18–20, row 78 columns 21–21, row 78 columns 22–22, row 78 columns 23–23,
row 78 columns 24–24, row 78 columns 25–25, row 78 columns 26–26, row 78 columns 27–27, row 78 columns 28–28, row 78
columns 29–29, row 78 columns 30–30, row 78 columns 31–32, row 78 columns 33–34, row 78 columns 35–36), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1748 : rowsJ2 77 78 75 76 ≤ 258708892133 := by decide +kernel

theorem rows22250R_1749 : rowsJ2 77 78 76 77 ≤ 157323332855 := by decide +kernel

theorem rows22250R_1750 : rowsJ2 77 78 77 360 ≤ 52832112824 := by decide +kernel

theorem rows22250R_1751 : rowsJ2 78 79 0 18 ≤ 376797708676 := by decide +kernel

theorem rows22250R_1752 : rowsJ2 78 79 18 21 ≤ 0 := by decide +kernel

theorem rows22250R_1753 : rowsJ2 78 79 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1754 : rowsJ2 78 79 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1755 : rowsJ2 78 79 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1756 : rowsJ2 78 79 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1757 : rowsJ2 78 79 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1758 : rowsJ2 78 79 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1759 : rowsJ2 78 79 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1760 : rowsJ2 78 79 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1761 : rowsJ2 78 79 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1762 : rowsJ2 78 79 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1763 : rowsJ2 78 79 31 33 ≤ 0 := by decide +kernel

theorem rows22250R_1764 : rowsJ2 78 79 33 35 ≤ 0 := by decide +kernel

theorem rows22250R_1765 : rowsJ2 78 79 35 37 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1748
#print axioms SieveCert.rows22250R_1765
