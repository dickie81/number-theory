/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 357–367 of 5796

File 32 of 465: the parts `rows22250R_357` … `rows22250R_367` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95540 tests: row 42 columns 41–41, row 42 columns 42–359, row 43 columns
0–13, row 43 columns 14–16, row 43 columns 17–19, row 43 columns 20–21, row 43 columns 22–23, row 43 columns 24–25,
row 43 columns 26–26, row 43 columns 27–27, row 43 columns 28–28), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_357 : rowsJ2 42 43 41 42 ≤ 198695958254 := by decide +kernel

theorem rows22250R_358 : rowsJ2 42 43 42 360 ≤ 172249083412 := by decide +kernel

theorem rows22250R_359 : rowsJ2 43 44 0 14 ≤ 741622449781 := by decide +kernel

theorem rows22250R_360 : rowsJ2 43 44 14 17 ≤ 1715993865718 := by decide +kernel

theorem rows22250R_361 : rowsJ2 43 44 17 20 ≤ 2216785957329 := by decide +kernel

theorem rows22250R_362 : rowsJ2 43 44 20 22 ≤ 1440378437920 := by decide +kernel

theorem rows22250R_363 : rowsJ2 43 44 22 24 ≤ 1278438023379 := by decide +kernel

theorem rows22250R_364 : rowsJ2 43 44 24 26 ≤ 1072630644676 := by decide +kernel

theorem rows22250R_365 : rowsJ2 43 44 26 27 ≤ 462543589495 := by decide +kernel

theorem rows22250R_366 : rowsJ2 43 44 27 28 ≤ 418546464044 := by decide +kernel

theorem rows22250R_367 : rowsJ2 43 44 28 29 ≤ 378496365731 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_357
#print axioms SieveCert.rows22250R_367
