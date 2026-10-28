/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 0–15 of 5066

File 1 of 387: the parts `rows22240R_0` … `rows22240R_15` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99929 in units of a depth-4 test: rows 0–9, rows 10–11, rows 12–12,
rows 13–13, row 14 columns 0–13, row 14 columns 14–339, row 15 columns 0–13, row 15 columns 14–339, row 16 columns
0–13, row 16 columns 14–339, row 17 columns 0–13, row 17 columns 14–16, row 17 columns 17–339, row 18 columns 0–13,
row 18 columns 14–16, row 18 columns 17–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_0 : rows2 0 10 ≤ 9692105917449 := by decide +kernel

theorem rows22240R_1 : rows2 10 12 ≤ 8576062139777 := by decide +kernel

theorem rows22240R_2 : rows2 12 13 ≤ 5421418159221 := by decide +kernel

theorem rows22240R_3 : rows2 13 14 ≤ 5933935082104 := by decide +kernel

theorem rows22240R_4 : rowsJ2 14 15 0 14 ≤ 5592527837229 := by decide +kernel

theorem rows22240R_5 : rowsJ2 14 15 14 340 ≤ 650139437797 := by decide +kernel

theorem rows22240R_6 : rowsJ2 15 16 0 14 ≤ 5250722583508 := by decide +kernel

theorem rows22240R_7 : rowsJ2 15 16 14 340 ≤ 1099599741060 := by decide +kernel

theorem rows22240R_8 : rowsJ2 16 17 0 14 ≤ 4910960885911 := by decide +kernel

theorem rows22240R_9 : rowsJ2 16 17 14 340 ≤ 1428370862264 := by decide +kernel

theorem rows22240R_10 : rowsJ2 17 18 0 14 ≤ 4576033395993 := by decide +kernel

theorem rows22240R_11 : rowsJ2 17 18 14 17 ≤ 1265508748202 := by decide +kernel

theorem rows22240R_12 : rowsJ2 17 18 17 340 ≤ 492560270182 := by decide +kernel

theorem rows22240R_13 : rowsJ2 18 19 0 14 ≤ 4245478662219 := by decide +kernel

theorem rows22240R_14 : rowsJ2 18 19 14 17 ≤ 1131804868985 := by decide +kernel

theorem rows22240R_15 : rowsJ2 18 19 17 340 ≤ 1131166356201 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_0
#print axioms SieveCert.rows22240R_15
