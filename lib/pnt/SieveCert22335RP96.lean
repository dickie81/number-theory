/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 368–371 of 549

File 96 of 140: the parts `rows22335R_368` … `rows22335R_371` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29299 tests: row 109 columns 70–299, row 110 columns 0–50, row 110 columns
51–56, row 110 columns 57–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_368 : rowsJ2 109 110 70 300 ≤ 340015824642289 := by decide +kernel

theorem rows22335R_369 : rowsJ2 110 111 0 51 ≤ 308197969670839 := by decide +kernel

theorem rows22335R_370 : rowsJ2 110 111 51 57 ≤ 40681188469470 := by decide +kernel

theorem rows22335R_371 : rowsJ2 110 111 57 63 ≤ 21295441642841 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_368
#print axioms SieveCert.rows22335R_371
