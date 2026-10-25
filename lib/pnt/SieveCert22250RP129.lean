/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1453–1470 of 4715

File 129 of 351: the parts `rows22250R_1453` … `rows22250R_1470` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 99638 tests: row 72 columns 69–69, row 72 columns 70–70, row 72 columns
71–71, row 72 columns 72–339, row 73 columns 0–17, row 73 columns 18–19, row 73 columns 20–21, row 73 columns 22–22,
row 73 columns 23–23, row 73 columns 24–24, row 73 columns 25–25, row 73 columns 26–26, row 73 columns 27–27, row 73
columns 28–29, row 73 columns 30–31, row 73 columns 32–33, row 73 columns 34–36, row 73 columns 37–38), each a sum
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

theorem rows22250R_1453 : rowsJ2 72 73 69 70 ≤ 567280356704 := by decide +kernel

theorem rows22250R_1454 : rowsJ2 72 73 70 71 ≤ 382958763536 := by decide +kernel

theorem rows22250R_1455 : rowsJ2 72 73 71 72 ≤ 259027660300 := by decide +kernel

theorem rows22250R_1456 : rowsJ2 72 73 72 340 ≤ 131176401151 := by decide +kernel

theorem rows22250R_1457 : rowsJ2 73 74 0 18 ≤ 529008445880 := by decide +kernel

theorem rows22250R_1458 : rowsJ2 73 74 18 20 ≤ 0 := by decide +kernel

theorem rows22250R_1459 : rowsJ2 73 74 20 22 ≤ 0 := by decide +kernel

theorem rows22250R_1460 : rowsJ2 73 74 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1461 : rowsJ2 73 74 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1462 : rowsJ2 73 74 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1463 : rowsJ2 73 74 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1464 : rowsJ2 73 74 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1465 : rowsJ2 73 74 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1466 : rowsJ2 73 74 28 30 ≤ 0 := by decide +kernel

theorem rows22250R_1467 : rowsJ2 73 74 30 32 ≤ 0 := by decide +kernel

theorem rows22250R_1468 : rowsJ2 73 74 32 34 ≤ 0 := by decide +kernel

theorem rows22250R_1469 : rowsJ2 73 74 34 37 ≤ 0 := by decide +kernel

theorem rows22250R_1470 : rowsJ2 73 74 37 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1453
#print axioms SieveCert.rows22250R_1470
