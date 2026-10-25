/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 0–15 of 5796

File 1 of 465: the parts `rows22250R_0` … `rows22250R_15` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99929 tests: rows 0–9, rows 10–11, rows 12–12, rows 13–13, row 14 columns
0–13, row 14 columns 14–359, row 15 columns 0–13, row 15 columns 14–359, row 16 columns 0–13, row 16 columns 14–359,
row 17 columns 0–13, row 17 columns 14–16, row 17 columns 17–359, row 18 columns 0–13, row 18 columns 14–16, row 18
columns 17–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_0 : rows2 0 10 ≤ 7287572873813 := by decide +kernel

theorem rows22250R_1 : rows2 10 12 ≤ 6177541068576 := by decide +kernel

theorem rows22250R_2 : rows2 12 13 ≤ 3714650727021 := by decide +kernel

theorem rows22250R_3 : rows2 13 14 ≤ 3941062887974 := by decide +kernel

theorem rows22250R_4 : rowsJ2 14 15 0 14 ≤ 3667994039889 := by decide +kernel

theorem rows22250R_5 : rowsJ2 14 15 14 360 ≤ 344522394745 := by decide +kernel

theorem rows22250R_6 : rowsJ2 15 16 0 14 ≤ 3398672806565 := by decide +kernel

theorem rows22250R_7 : rowsJ2 15 16 14 360 ≤ 570248309218 := by decide +kernel

theorem rows22250R_8 : rowsJ2 16 17 0 14 ≤ 3135507431213 := by decide +kernel

theorem rows22250R_9 : rowsJ2 16 17 14 360 ≤ 747146809748 := by decide +kernel

theorem rows22250R_10 : rowsJ2 17 18 0 14 ≤ 2880855164198 := by decide +kernel

theorem rows22250R_11 : rowsJ2 17 18 14 17 ≤ 669001896025 := by decide +kernel

theorem rows22250R_12 : rowsJ2 17 18 17 360 ≤ 301794787813 := by decide +kernel

theorem rows22250R_13 : rowsJ2 18 19 0 14 ≤ 2634846954242 := by decide +kernel

theorem rows22250R_14 : rowsJ2 18 19 14 17 ≤ 597689535403 := by decide +kernel

theorem rows22250R_15 : rowsJ2 18 19 17 360 ≤ 750503368364 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_0
#print axioms SieveCert.rows22250R_15
