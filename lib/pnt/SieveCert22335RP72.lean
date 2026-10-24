/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 277–280 of 549

File 72 of 140: the parts `rows22335R_277` … `rows22335R_280` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25389 tests: row 94 columns 77–83, row 94 columns 84–299, row 95 columns
0–52, row 95 columns 53–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_277 : rowsJ2 94 95 77 84 ≤ 35420326102391 := by decide +kernel

theorem rows22335R_278 : rowsJ2 94 95 84 300 ≤ 1184826447113052 := by decide +kernel

theorem rows22335R_279 : rowsJ2 95 96 0 53 ≤ 589950815631349 := by decide +kernel

theorem rows22335R_280 : rowsJ2 95 96 53 61 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_277
#print axioms SieveCert.rows22335R_280
