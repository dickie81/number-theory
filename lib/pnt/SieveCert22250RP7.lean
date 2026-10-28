/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 101–116 of 4715

File 7 of 351: the parts `rows22250R_101` … `rows22250R_116` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 93003 in units of a depth-4 test: row 29 columns 14–16, row 29 columns
17–18, row 29 columns 19–20, row 29 columns 21–21, row 29 columns 22–22, row 29 columns 23–23, row 29 columns 24–24,
row 29 columns 25–25, row 29 columns 26–26, row 29 columns 27–27, row 29 columns 28–28, row 29 columns 29–339, row
30 columns 0–13, row 30 columns 14–16, row 30 columns 17–18, row 30 columns 19–20), each a sum of refined costs
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

theorem rows22250R_101 : rowsJ2 29 30 14 17 ≤ 1690621557589 := by decide +kernel

theorem rows22250R_102 : rowsJ2 29 30 17 19 ≤ 2181681951161 := by decide +kernel

theorem rows22250R_103 : rowsJ2 29 30 19 21 ≤ 2798956764248 := by decide +kernel

theorem rows22250R_104 : rowsJ2 29 30 21 22 ≤ 1504238918035 := by decide +kernel

theorem rows22250R_105 : rowsJ2 29 30 22 23 ≤ 1543654411448 := by decide +kernel

theorem rows22250R_106 : rowsJ2 29 30 23 24 ≤ 1553461435724 := by decide +kernel

theorem rows22250R_107 : rowsJ2 29 30 24 25 ≤ 1527305549964 := by decide +kernel

theorem rows22250R_108 : rowsJ2 29 30 25 26 ≤ 1466204275404 := by decide +kernel

theorem rows22250R_109 : rowsJ2 29 30 26 27 ≤ 1397249130202 := by decide +kernel

theorem rows22250R_110 : rowsJ2 29 30 27 28 ≤ 1314122969872 := by decide +kernel

theorem rows22250R_111 : rowsJ2 29 30 28 29 ≤ 1228281177733 := by decide +kernel

theorem rows22250R_112 : rowsJ2 29 30 29 340 ≤ 1140056768927 := by decide +kernel

theorem rows22250R_113 : rowsJ2 30 31 0 14 ≤ 723576970983 := by decide +kernel

theorem rows22250R_114 : rowsJ2 30 31 14 17 ≤ 1794726779786 := by decide +kernel

theorem rows22250R_115 : rowsJ2 30 31 17 19 ≤ 2209342207147 := by decide +kernel

theorem rows22250R_116 : rowsJ2 30 31 19 21 ≤ 2744126757707 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_101
#print axioms SieveCert.rows22250R_116
