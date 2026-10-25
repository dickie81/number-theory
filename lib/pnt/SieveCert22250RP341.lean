/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4547–4564 of 4715

File 341 of 351: the parts `rows22250R_4547` … `rows22250R_4564` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, 96319 tests: row 180 columns 43–43, row 180 columns 44–44, row 180 columns
45–45, row 180 columns 46–93, row 180 columns 94–339, row 181 columns 0–33, row 181 columns 34–35, row 181 columns
36–37, row 181 columns 38–38, row 181 columns 39–39, row 181 columns 40–40, row 181 columns 41–41, row 181 columns
42–42, row 181 columns 43–43, row 181 columns 44–44, row 181 columns 45–45, row 181 columns 46–339, row 182 columns
0–32), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4547 : rowsJ2 180 181 43 44 ≤ 24783032454124 := by decide +kernel

theorem rows22250R_4548 : rowsJ2 180 181 44 45 ≤ 22145349309990 := by decide +kernel

theorem rows22250R_4549 : rowsJ2 180 181 45 46 ≤ 19681050743722 := by decide +kernel

theorem rows22250R_4550 : rowsJ2 180 181 46 94 ≤ 131017729377400 := by decide +kernel

theorem rows22250R_4551 : rowsJ2 180 181 94 340 ≤ 3076284934951165 := by decide +kernel

theorem rows22250R_4552 : rowsJ2 181 182 0 34 ≤ 23104315882575 := by decide +kernel

theorem rows22250R_4553 : rowsJ2 181 182 34 36 ≤ 23887344966759 := by decide +kernel

theorem rows22250R_4554 : rowsJ2 181 182 36 38 ≤ 34971383494586 := by decide +kernel

theorem rows22250R_4555 : rowsJ2 181 182 38 39 ≤ 20505030612182 := by decide +kernel

theorem rows22250R_4556 : rowsJ2 181 182 39 40 ≤ 22622905885716 := by decide +kernel

theorem rows22250R_4557 : rowsJ2 181 182 40 41 ≤ 24816722042670 := by decide +kernel

theorem rows22250R_4558 : rowsJ2 181 182 41 42 ≤ 27084682261722 := by decide +kernel

theorem rows22250R_4559 : rowsJ2 181 182 42 43 ≤ 26780469869336 := by decide +kernel

theorem rows22250R_4560 : rowsJ2 181 182 43 44 ≤ 23989793339050 := by decide +kernel

theorem rows22250R_4561 : rowsJ2 181 182 44 45 ≤ 21380328028680 := by decide +kernel

theorem rows22250R_4562 : rowsJ2 181 182 45 46 ≤ 18945410198479 := by decide +kernel

theorem rows22250R_4563 : rowsJ2 181 182 46 340 ≤ 3326006015110967 := by decide +kernel

theorem rows22250R_4564 : rowsJ2 182 183 0 33 ≤ 17699968395828 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4547
#print axioms SieveCert.rows22250R_4564
