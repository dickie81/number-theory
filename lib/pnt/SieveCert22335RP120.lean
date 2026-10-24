/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 462–465 of 549

File 120 of 140: the parts `rows22335R_462` … `rows22335R_465` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25864 tests: row 133 columns 0–43, row 133 columns 44–52, row 133 columns
53–299, row 134 columns 0–42), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_462 : rowsJ2 133 134 0 44 ≤ 135283768150648 := by decide +kernel

theorem rows22335R_463 : rowsJ2 133 134 44 53 ≤ 101118363384192 := by decide +kernel

theorem rows22335R_464 : rowsJ2 133 134 53 300 ≤ 2666475438920281 := by decide +kernel

theorem rows22335R_465 : rowsJ2 134 135 0 43 ≤ 123420864373718 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_462
#print axioms SieveCert.rows22335R_465
