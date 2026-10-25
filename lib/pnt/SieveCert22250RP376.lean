/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4547–4562 of 5796

File 376 of 465: the parts `rows22250R_4547` … `rows22250R_4562` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99097 tests: row 146 columns 74–74, row 146 columns 75–75, row 146 columns
76–76, row 146 columns 77–77, row 146 columns 78–78, row 146 columns 79–80, row 146 columns 81–83, row 146 columns
84–88, row 146 columns 89–359, row 147 columns 0–23, row 147 columns 24–48, row 147 columns 49–52, row 147 columns
53–54, row 147 columns 55–56, row 147 columns 57–57, row 147 columns 58–58), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4547 : rowsJ2 146 147 74 75 ≤ 5119065669843 := by decide +kernel

theorem rows22250R_4548 : rowsJ2 146 147 75 76 ≤ 4464373944782 := by decide +kernel

theorem rows22250R_4549 : rowsJ2 146 147 76 77 ≤ 3861961633281 := by decide +kernel

theorem rows22250R_4550 : rowsJ2 146 147 77 78 ≤ 3293072527672 := by decide +kernel

theorem rows22250R_4551 : rowsJ2 146 147 78 79 ≤ 2774438555871 := by decide +kernel

theorem rows22250R_4552 : rowsJ2 146 147 79 81 ≤ 4135616025550 := by decide +kernel

theorem rows22250R_4553 : rowsJ2 146 147 81 84 ≤ 3388358540949 := by decide +kernel

theorem rows22250R_4554 : rowsJ2 146 147 84 89 ≤ 4751424240953 := by decide +kernel

theorem rows22250R_4555 : rowsJ2 146 147 89 360 ≤ 622062552023079 := by decide +kernel

theorem rows22250R_4556 : rowsJ2 147 148 0 24 ≤ 2520605055942 := by decide +kernel

theorem rows22250R_4557 : rowsJ2 147 148 24 49 ≤ 1465014063928 := by decide +kernel

theorem rows22250R_4558 : rowsJ2 147 148 49 53 ≤ 4465073907708 := by decide +kernel

theorem rows22250R_4559 : rowsJ2 147 148 53 55 ≤ 4689109630983 := by decide +kernel

theorem rows22250R_4560 : rowsJ2 147 148 55 57 ≤ 6799348888770 := by decide +kernel

theorem rows22250R_4561 : rowsJ2 147 148 57 58 ≤ 4291194273023 := by decide +kernel

theorem rows22250R_4562 : rowsJ2 147 148 58 59 ≤ 4935716181907 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4547
#print axioms SieveCert.rows22250R_4562
