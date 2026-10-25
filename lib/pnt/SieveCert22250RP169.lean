/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1698–1715 of 5796

File 169 of 465: the parts `rows22250R_1698` … `rows22250R_1715` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 98908 tests: row 77 columns 19–20, row 77 columns 21–21, row 77 columns
22–22, row 77 columns 23–23, row 77 columns 24–24, row 77 columns 25–25, row 77 columns 26–26, row 77 columns 27–27,
row 77 columns 28–28, row 77 columns 29–29, row 77 columns 30–30, row 77 columns 31–31, row 77 columns 32–32, row 77
columns 33–34, row 77 columns 35–36, row 77 columns 37–38, row 77 columns 39–40, row 77 columns 41–42), each a sum
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

theorem rows22250R_1698 : rowsJ2 77 78 19 21 ≤ 0 := by decide +kernel

theorem rows22250R_1699 : rowsJ2 77 78 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1700 : rowsJ2 77 78 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1701 : rowsJ2 77 78 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1702 : rowsJ2 77 78 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1703 : rowsJ2 77 78 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1704 : rowsJ2 77 78 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1705 : rowsJ2 77 78 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1706 : rowsJ2 77 78 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1707 : rowsJ2 77 78 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1708 : rowsJ2 77 78 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1709 : rowsJ2 77 78 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1710 : rowsJ2 77 78 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1711 : rowsJ2 77 78 33 35 ≤ 0 := by decide +kernel

theorem rows22250R_1712 : rowsJ2 77 78 35 37 ≤ 0 := by decide +kernel

theorem rows22250R_1713 : rowsJ2 77 78 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1714 : rowsJ2 77 78 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1715 : rowsJ2 77 78 41 43 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1698
#print axioms SieveCert.rows22250R_1715
