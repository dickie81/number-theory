/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 97–113 of 5066

File 7 of 387: the parts `rows22240R_97` … `rows22240R_113` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 96995 in units of a depth-4 test: row 28 columns 25–25, row 28 columns
26–26, row 28 columns 27–27, row 28 columns 28–339, row 29 columns 0–13, row 29 columns 14–16, row 29 columns 17–18,
row 29 columns 19–19, row 29 columns 20–20, row 29 columns 21–21, row 29 columns 22–22, row 29 columns 23–23, row 29
columns 24–24, row 29 columns 25–25, row 29 columns 26–26, row 29 columns 27–27, row 29 columns 28–28), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_97 : rowsJ2 28 29 25 26 ≤ 1756213669064 := by decide +kernel

theorem rows22240R_98 : rowsJ2 28 29 26 27 ≤ 1748161104965 := by decide +kernel

theorem rows22240R_99 : rowsJ2 28 29 27 28 ≤ 1702739008397 := by decide +kernel

theorem rows22240R_100 : rowsJ2 28 29 28 340 ≤ 1639695406360 := by decide +kernel

theorem rows22240R_101 : rowsJ2 29 30 0 14 ≤ 1396328948141 := by decide +kernel

theorem rows22240R_102 : rowsJ2 29 30 14 17 ≤ 1010298724405 := by decide +kernel

theorem rows22240R_103 : rowsJ2 29 30 17 19 ≤ 1721315564363 := by decide +kernel

theorem rows22240R_104 : rowsJ2 29 30 19 20 ≤ 1190059982795 := by decide +kernel

theorem rows22240R_105 : rowsJ2 29 30 20 21 ≤ 1369828499004 := by decide +kernel

theorem rows22240R_106 : rowsJ2 29 30 21 22 ≤ 1520523303776 := by decide +kernel

theorem rows22240R_107 : rowsJ2 29 30 22 23 ≤ 1617172269142 := by decide +kernel

theorem rows22240R_108 : rowsJ2 29 30 23 24 ≤ 1665956456614 := by decide +kernel

theorem rows22240R_109 : rowsJ2 29 30 24 25 ≤ 1683837470725 := by decide +kernel

theorem rows22240R_110 : rowsJ2 29 30 25 26 ≤ 1691480300489 := by decide +kernel

theorem rows22240R_111 : rowsJ2 29 30 26 27 ≤ 1665401888071 := by decide +kernel

theorem rows22240R_112 : rowsJ2 29 30 27 28 ≤ 1614127835256 := by decide +kernel

theorem rows22240R_113 : rowsJ2 29 30 28 29 ≤ 1545405758859 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_97
#print axioms SieveCert.rows22240R_113
