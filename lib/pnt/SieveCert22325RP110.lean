/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 424–427 of 561

File 110 of 142: the parts `rows22325R_424` … `rows22325R_427` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29871 tests: row 119 columns 48–54, row 119 columns 55–62, row 119 columns
63–299, row 120 columns 0–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_424 : rowsJ2 119 120 48 55 ≤ 82151275404317 := by decide +kernel

theorem rows22325R_425 : rowsJ2 119 120 55 63 ≤ 43121880212566 := by decide +kernel

theorem rows22325R_426 : rowsJ2 119 120 63 300 ≤ 306452859100107 := by decide +kernel

theorem rows22325R_427 : rowsJ2 120 121 0 48 ≤ 191118434403772 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_424
#print axioms SieveCert.rows22325R_427
