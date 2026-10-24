/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 368–371 of 561

File 96 of 142: the parts `rows22325R_368` … `rows22325R_371` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28168 tests: row 108 columns 51–56, row 108 columns 57–61, row 108 columns
62–67, row 108 columns 68–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_368 : rowsJ2 108 109 51 57 ≤ 32624548809528 := by decide +kernel

theorem rows22325R_369 : rowsJ2 108 109 57 62 ≤ 17089988177522 := by decide +kernel

theorem rows22325R_370 : rowsJ2 108 109 62 68 ≤ 1632488852544 := by decide +kernel

theorem rows22325R_371 : rowsJ2 108 109 68 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_368
#print axioms SieveCert.rows22325R_371
