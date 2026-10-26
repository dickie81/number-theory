/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 394–397 of 561

File 103 of 143: the parts `rows22322R_394` … `rows22322R_397` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27029 tests: row 113 columns 50–55, row 113 columns 56–61, row 113 columns
62–69, row 113 columns 70–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_394 : rowsJ2 113 114 50 56 ≤ 52754923218941 := by decide +kernel

theorem rows22322R_395 : rowsJ2 113 114 56 62 ≤ 33021604626158 := by decide +kernel

theorem rows22322R_396 : rowsJ2 113 114 62 70 ≤ 8779446215455 := by decide +kernel

theorem rows22322R_397 : rowsJ2 113 114 70 300 ≤ 108432281193108 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_394
#print axioms SieveCert.rows22322R_397
