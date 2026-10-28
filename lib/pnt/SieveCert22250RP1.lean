/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 0–15 of 4715

File 1 of 351: the parts `rows22250R_0` … `rows22250R_15` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 99849 in units of a depth-4 test: rows 0–9, rows 10–11, rows 12–12,
rows 13–13, row 14 columns 0–13, row 14 columns 14–339, row 15 columns 0–13, row 15 columns 14–339, row 16 columns
0–13, row 16 columns 14–339, row 17 columns 0–13, row 17 columns 14–16, row 17 columns 17–339, row 18 columns 0–13,
row 18 columns 14–16, row 18 columns 17–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound,
by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_0 : rows2 0 10 ≤ 9928104671330 := by decide +kernel

theorem rows22250R_1 : rows2 10 12 ≤ 7719029714452 := by decide +kernel

theorem rows22250R_2 : rows2 12 13 ≤ 4389900043861 := by decide +kernel

theorem rows22250R_3 : rows2 13 14 ≤ 4501099437982 := by decide +kernel

theorem rows22250R_4 : rowsJ2 14 15 0 14 ≤ 4132446212626 := by decide +kernel

theorem rows22250R_5 : rowsJ2 14 15 14 340 ≤ 329941092695 := by decide +kernel

theorem rows22250R_6 : rowsJ2 15 16 0 14 ≤ 3777210556945 := by decide +kernel

theorem rows22250R_7 : rowsJ2 15 16 14 340 ≤ 576469125419 := by decide +kernel

theorem rows22250R_8 : rowsJ2 16 17 0 14 ≤ 3442270379362 := by decide +kernel

theorem rows22250R_9 : rowsJ2 16 17 14 340 ≤ 875513156404 := by decide +kernel

theorem rows22250R_10 : rowsJ2 17 18 0 14 ≤ 3119528774121 := by decide +kernel

theorem rows22250R_11 : rowsJ2 17 18 14 17 ≤ 827031875239 := by decide +kernel

theorem rows22250R_12 : rowsJ2 17 18 17 340 ≤ 559113412994 := by decide +kernel

theorem rows22250R_13 : rowsJ2 18 19 0 14 ≤ 2816152375287 := by decide +kernel

theorem rows22250R_14 : rowsJ2 18 19 14 17 ≤ 817066648242 := by decide +kernel

theorem rows22250R_15 : rowsJ2 18 19 17 340 ≤ 1406731800315 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_0
#print axioms SieveCert.rows22250R_15
