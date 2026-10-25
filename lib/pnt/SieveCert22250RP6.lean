/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 83–100 of 4715

File 6 of 351: the parts `rows22250R_83` … `rows22250R_100` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 98179 tests: row 27 columns 23–23, row 27 columns 24–24, row 27 columns
25–25, row 27 columns 26–26, row 27 columns 27–339, row 28 columns 0–13, row 28 columns 14–16, row 28 columns 17–18,
row 28 columns 19–20, row 28 columns 21–21, row 28 columns 22–22, row 28 columns 23–23, row 28 columns 24–24, row 28
columns 25–25, row 28 columns 26–26, row 28 columns 27–27, row 28 columns 28–339, row 29 columns 0–13), each a sum
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

theorem rows22250R_83 : rowsJ2 27 28 23 24 ≤ 1673323066356 := by decide +kernel

theorem rows22250R_84 : rowsJ2 27 28 24 25 ≤ 1681512337307 := by decide +kernel

theorem rows22250R_85 : rowsJ2 27 28 25 26 ≤ 1647431456637 := by decide +kernel

theorem rows22250R_86 : rowsJ2 27 28 26 27 ≤ 1585008332337 := by decide +kernel

theorem rows22250R_87 : rowsJ2 27 28 27 340 ≤ 1508345648565 := by decide +kernel

theorem rows22250R_88 : rowsJ2 28 29 0 14 ≤ 836899974265 := by decide +kernel

theorem rows22250R_89 : rowsJ2 28 29 14 17 ≤ 1582721526326 := by decide +kernel

theorem rows22250R_90 : rowsJ2 28 29 17 19 ≤ 2146621999080 := by decide +kernel

theorem rows22250R_91 : rowsJ2 28 29 19 21 ≤ 2838916791044 := by decide +kernel

theorem rows22250R_92 : rowsJ2 28 29 21 22 ≤ 1554166596286 := by decide +kernel

theorem rows22250R_93 : rowsJ2 28 29 22 23 ≤ 1592033860924 := by decide +kernel

theorem rows22250R_94 : rowsJ2 28 29 23 24 ≤ 1617969291039 := by decide +kernel

theorem rows22250R_95 : rowsJ2 28 29 24 25 ≤ 1605689879827 := by decide +kernel

theorem rows22250R_96 : rowsJ2 28 29 25 26 ≤ 1557929319768 := by decide +kernel

theorem rows22250R_97 : rowsJ2 28 29 26 27 ≤ 1489016593159 := by decide +kernel

theorem rows22250R_98 : rowsJ2 28 29 27 28 ≤ 1412372335452 := by decide +kernel

theorem rows22250R_99 : rowsJ2 28 29 28 340 ≤ 1325129474007 := by decide +kernel

theorem rows22250R_100 : rowsJ2 29 30 0 14 ≤ 769586939652 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_83
#print axioms SieveCert.rows22250R_100
