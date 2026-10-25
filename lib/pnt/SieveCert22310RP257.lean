/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1026–1029 of 1732

File 257 of 430: the parts `rows22310R_1026` … `rows22310R_1029` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28704 tests: row 135 columns 84–86, row 135 columns 87–89, row 135 columns
90–92, row 135 columns 93–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1026 : rowsJ2 135 136 84 87 ≤ 0 := by decide +kernel

theorem rows22310R_1027 : rowsJ2 135 136 87 90 ≤ 0 := by decide +kernel

theorem rows22310R_1028 : rowsJ2 135 136 90 93 ≤ 0 := by decide +kernel

theorem rows22310R_1029 : rowsJ2 135 136 93 96 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1026
#print axioms SieveCert.rows22310R_1029
