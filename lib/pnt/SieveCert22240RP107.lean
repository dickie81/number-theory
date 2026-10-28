/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1092–1103 of 5066

File 107 of 387: the parts `rows22240R_1092` … `rows22240R_1103` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 96768 in units of a depth-4 test: row 64 columns 43–43, row 64 columns
44–44, row 64 columns 45–45, row 64 columns 46–46, row 64 columns 47–47, row 64 columns 48–48, row 64 columns 49–49,
row 64 columns 50–50, row 64 columns 51–51, row 64 columns 52–52, row 64 columns 53–53, row 64 columns 54–54), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1092 : rowsJ2 64 65 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1093 : rowsJ2 64 65 44 45 ≤ 67433681154 := by decide +kernel

theorem rows22240R_1094 : rowsJ2 64 65 45 46 ≤ 197205897106 := by decide +kernel

theorem rows22240R_1095 : rowsJ2 64 65 46 47 ≤ 384579134927 := by decide +kernel

theorem rows22240R_1096 : rowsJ2 64 65 47 48 ≤ 821108441357 := by decide +kernel

theorem rows22240R_1097 : rowsJ2 64 65 48 49 ≤ 1568727475619 := by decide +kernel

theorem rows22240R_1098 : rowsJ2 64 65 49 50 ≤ 2419183649089 := by decide +kernel

theorem rows22240R_1099 : rowsJ2 64 65 50 51 ≤ 3300957844527 := by decide +kernel

theorem rows22240R_1100 : rowsJ2 64 65 51 52 ≤ 4343233673955 := by decide +kernel

theorem rows22240R_1101 : rowsJ2 64 65 52 53 ≤ 5676797805976 := by decide +kernel

theorem rows22240R_1102 : rowsJ2 64 65 53 54 ≤ 6837572968380 := by decide +kernel

theorem rows22240R_1103 : rowsJ2 64 65 54 55 ≤ 7824296182914 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1092
#print axioms SieveCert.rows22240R_1103
