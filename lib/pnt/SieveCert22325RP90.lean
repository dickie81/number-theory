/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 344–347 of 561

File 90 of 142: the parts `rows22325R_344` … `rows22325R_347` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28952 tests: row 104 columns 52–57, row 104 columns 58–62, row 104 columns
63–68, row 104 columns 69–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_344 : rowsJ2 104 105 52 58 ≤ 16705198475003 := by decide +kernel

theorem rows22325R_345 : rowsJ2 104 105 58 63 ≤ 2318237371203 := by decide +kernel

theorem rows22325R_346 : rowsJ2 104 105 63 69 ≤ 0 := by decide +kernel

theorem rows22325R_347 : rowsJ2 104 105 69 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_344
#print axioms SieveCert.rows22325R_347
