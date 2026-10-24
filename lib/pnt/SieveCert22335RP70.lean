/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 270–273 of 549

File 70 of 140: the parts `rows22335R_270` … `rows22335R_273` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26218 tests: row 93 columns 77–83, row 93 columns 84–299, row 94 columns
0–52, row 94 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_270 : rowsJ2 93 94 77 84 ≤ 33207194683365 := by decide +kernel

theorem rows22335R_271 : rowsJ2 93 94 84 300 ≤ 963784566892618 := by decide +kernel

theorem rows22335R_272 : rowsJ2 94 95 0 53 ≤ 614206575263702 := by decide +kernel

theorem rows22335R_273 : rowsJ2 94 95 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_270
#print axioms SieveCert.rows22335R_273
