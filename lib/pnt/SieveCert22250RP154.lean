/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1799–1814 of 4715

File 154 of 351: the parts `rows22250R_1799` … `rows22250R_1814` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 96624 in units of a depth-4 test: row 80 columns 64–64, row 80 columns
65–66, row 80 columns 67–68, row 80 columns 69–70, row 80 columns 71–73, row 80 columns 74–76, row 80 columns 77–78,
row 80 columns 79–79, row 80 columns 80–339, row 81 columns 0–16, row 81 columns 17–18, row 81 columns 19–20, row 81
columns 21–22, row 81 columns 23–24, row 81 columns 25–27, row 81 columns 28–31), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1799 : rowsJ2 80 81 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_1800 : rowsJ2 80 81 65 67 ≤ 0 := by decide +kernel

theorem rows22250R_1801 : rowsJ2 80 81 67 69 ≤ 0 := by decide +kernel

theorem rows22250R_1802 : rowsJ2 80 81 69 71 ≤ 0 := by decide +kernel

theorem rows22250R_1803 : rowsJ2 80 81 71 74 ≤ 0 := by decide +kernel

theorem rows22250R_1804 : rowsJ2 80 81 74 77 ≤ 125343115929 := by decide +kernel

theorem rows22250R_1805 : rowsJ2 80 81 77 79 ≤ 1385580748784 := by decide +kernel

theorem rows22250R_1806 : rowsJ2 80 81 79 80 ≤ 1671878769099 := by decide +kernel

theorem rows22250R_1807 : rowsJ2 80 81 80 340 ≤ 2090125257226 := by decide +kernel

theorem rows22250R_1808 : rowsJ2 81 82 0 17 ≤ 61836282793 := by decide +kernel

theorem rows22250R_1809 : rowsJ2 81 82 17 19 ≤ 9304795507 := by decide +kernel

theorem rows22250R_1810 : rowsJ2 81 82 19 21 ≤ 2062616007 := by decide +kernel

theorem rows22250R_1811 : rowsJ2 81 82 21 23 ≤ 0 := by decide +kernel

theorem rows22250R_1812 : rowsJ2 81 82 23 25 ≤ 0 := by decide +kernel

theorem rows22250R_1813 : rowsJ2 81 82 25 28 ≤ 0 := by decide +kernel

theorem rows22250R_1814 : rowsJ2 81 82 28 32 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1799
#print axioms SieveCert.rows22250R_1814
