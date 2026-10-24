/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 188–191 of 549

File 49 of 140: the parts `rows22335R_188` … `rows22335R_191` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 28935 tests: row 82 columns 37–61, row 82 columns 62–67, row 82 columns
68–71, row 82 columns 72–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_188 : rowsJ2 82 83 37 62 ≤ 438907579536151 := by decide +kernel

theorem rows22335R_189 : rowsJ2 82 83 62 68 ≤ 2965742988029 := by decide +kernel

theorem rows22335R_190 : rowsJ2 82 83 68 72 ≤ 10086637726459 := by decide +kernel

theorem rows22335R_191 : rowsJ2 82 83 72 76 ≤ 8450324970768 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_188
#print axioms SieveCert.rows22335R_191
