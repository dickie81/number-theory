/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 427–430 of 549

File 111 of 140: the parts `rows22335R_427` … `rows22335R_430` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26557 tests: row 122 columns 54–62, row 122 columns 63–299, row 123 columns
0–46, row 123 columns 47–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22335R_427 : rowsJ2 122 123 54 63 ≤ 37636151258106 := by decide +kernel

theorem rows22335R_428 : rowsJ2 122 123 63 300 ≤ 878682174176729 := by decide +kernel

theorem rows22335R_429 : rowsJ2 123 124 0 47 ≤ 167397982013863 := by decide +kernel

theorem rows22335R_430 : rowsJ2 123 124 47 54 ≤ 86062223618590 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_427
#print axioms SieveCert.rows22335R_430
