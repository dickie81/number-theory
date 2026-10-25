/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1073–1076 of 1732

File 269 of 430: the parts `rows22310R_1073` … `rows22310R_1076` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29440 tests: row 138 columns 91–93, row 138 columns 94–97, row 138 columns
98–101, row 138 columns 102–106), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1073 : rowsJ2 138 139 91 94 ≤ 0 := by decide +kernel

theorem rows22310R_1074 : rowsJ2 138 139 94 98 ≤ 0 := by decide +kernel

theorem rows22310R_1075 : rowsJ2 138 139 98 102 ≤ 430216748507 := by decide +kernel

theorem rows22310R_1076 : rowsJ2 138 139 102 107 ≤ 10310393564369 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1073
#print axioms SieveCert.rows22310R_1076
