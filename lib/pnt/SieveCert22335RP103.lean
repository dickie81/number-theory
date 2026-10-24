/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 395–398 of 549

File 103 of 140: the parts `rows22335R_395` … `rows22335R_398` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25074 tests: row 115 columns 49–54, row 115 columns 55–61, row 115 columns
62–70, row 115 columns 71–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_395 : rowsJ2 115 116 49 55 ≤ 58205897008588 := by decide +kernel

theorem rows22335R_396 : rowsJ2 115 116 55 62 ≤ 38923393133565 := by decide +kernel

theorem rows22335R_397 : rowsJ2 115 116 62 71 ≤ 8181371029440 := by decide +kernel

theorem rows22335R_398 : rowsJ2 115 116 71 300 ≤ 1779466059218 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_395
#print axioms SieveCert.rows22335R_398
