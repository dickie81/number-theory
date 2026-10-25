/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1073–1081 of 4715

File 98 of 351: the parts `rows22250R_1073` … `rows22250R_1081` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 93791 tests: row 64 columns 48–48, row 64 columns 49–49, row 64 columns
50–50, row 64 columns 51–51, row 64 columns 52–52, row 64 columns 53–53, row 64 columns 54–54, row 64 columns 55–55,
row 64 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1073 : rowsJ2 64 65 48 49 ≤ 2283389283770 := by decide +kernel

theorem rows22250R_1074 : rowsJ2 64 65 49 50 ≤ 3123212178838 := by decide +kernel

theorem rows22250R_1075 : rowsJ2 64 65 50 51 ≤ 4195625468283 := by decide +kernel

theorem rows22250R_1076 : rowsJ2 64 65 51 52 ≤ 5497213351562 := by decide +kernel

theorem rows22250R_1077 : rowsJ2 64 65 52 53 ≤ 6552512375034 := by decide +kernel

theorem rows22250R_1078 : rowsJ2 64 65 53 54 ≤ 7499161967641 := by decide +kernel

theorem rows22250R_1079 : rowsJ2 64 65 54 55 ≤ 8423574504244 := by decide +kernel

theorem rows22250R_1080 : rowsJ2 64 65 55 56 ≤ 9376242136967 := by decide +kernel

theorem rows22250R_1081 : rowsJ2 64 65 56 57 ≤ 10092781043810 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1073
#print axioms SieveCert.rows22250R_1081
