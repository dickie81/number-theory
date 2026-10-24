/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 456–459 of 561

File 118 of 142: the parts `rows22325R_456` … `rows22325R_459` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 22655 tests: row 127 columns 46–52, row 127 columns 53–62, row 127 columns
63–299, row 128 columns 0–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_456 : rowsJ2 127 128 46 53 ≤ 95597763622896 := by decide +kernel

theorem rows22325R_457 : rowsJ2 127 128 53 63 ≤ 37159004510911 := by decide +kernel

theorem rows22325R_458 : rowsJ2 127 128 63 300 ≤ 1752727926617366 := by decide +kernel

theorem rows22325R_459 : rowsJ2 128 129 0 45 ≤ 135171485526677 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_456
#print axioms SieveCert.rows22325R_459
