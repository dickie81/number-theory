/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1798–1815 of 5796

File 177 of 465: the parts `rows22250R_1798` … `rows22250R_1815` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 92915 tests: row 78 columns 72–72, row 78 columns 73–73, row 78 columns
74–74, row 78 columns 75–75, row 78 columns 76–76, row 78 columns 77–77, row 78 columns 78–359, row 79 columns 0–17,
row 79 columns 18–20, row 79 columns 21–21, row 79 columns 22–22, row 79 columns 23–23, row 79 columns 24–24, row 79
columns 25–25, row 79 columns 26–26, row 79 columns 27–27, row 79 columns 28–28, row 79 columns 29–29), each a sum
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

theorem rows22250R_1798 : rowsJ2 78 79 72 73 ≤ 451172174570 := by decide +kernel

theorem rows22250R_1799 : rowsJ2 78 79 73 74 ≤ 304355125391 := by decide +kernel

theorem rows22250R_1800 : rowsJ2 78 79 74 75 ≤ 205687525064 := by decide +kernel

theorem rows22250R_1801 : rowsJ2 78 79 75 76 ≤ 104084297139 := by decide +kernel

theorem rows22250R_1802 : rowsJ2 78 79 76 77 ≤ 52835399032 := by decide +kernel

theorem rows22250R_1803 : rowsJ2 78 79 77 78 ≤ 0 := by decide +kernel

theorem rows22250R_1804 : rowsJ2 78 79 78 360 ≤ 0 := by decide +kernel

theorem rows22250R_1805 : rowsJ2 79 80 0 18 ≤ 312061348367 := by decide +kernel

theorem rows22250R_1806 : rowsJ2 79 80 18 21 ≤ 1416424677 := by decide +kernel

theorem rows22250R_1807 : rowsJ2 79 80 21 22 ≤ 2126514046 := by decide +kernel

theorem rows22250R_1808 : rowsJ2 79 80 22 23 ≤ 2127379146 := by decide +kernel

theorem rows22250R_1809 : rowsJ2 79 80 23 24 ≤ 1419509562 := by decide +kernel

theorem rows22250R_1810 : rowsJ2 79 80 24 25 ≤ 1421082650 := by decide +kernel

theorem rows22250R_1811 : rowsJ2 79 80 25 26 ≤ 711616528 := by decide +kernel

theorem rows22250R_1812 : rowsJ2 79 80 26 27 ≤ 712900658 := by decide +kernel

theorem rows22250R_1813 : rowsJ2 79 80 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1814 : rowsJ2 79 80 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1815 : rowsJ2 79 80 29 30 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1798
#print axioms SieveCert.rows22250R_1815
