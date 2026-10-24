/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 407–410 of 549

File 106 of 140: the parts `rows22335R_407` … `rows22335R_410` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24507 tests: row 117 columns 62–71, row 117 columns 72–299, row 118 columns
0–48, row 118 columns 49–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_407 : rowsJ2 117 118 62 72 ≤ 7009518253105 := by decide +kernel

theorem rows22335R_408 : rowsJ2 117 118 72 300 ≤ 0 := by decide +kernel

theorem rows22335R_409 : rowsJ2 118 119 0 49 ≤ 213363639366345 := by decide +kernel

theorem rows22335R_410 : rowsJ2 118 119 49 56 ≤ 74789647893792 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_407
#print axioms SieveCert.rows22335R_410
