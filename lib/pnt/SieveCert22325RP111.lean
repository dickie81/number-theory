/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 428–431 of 561

File 111 of 142: the parts `rows22325R_428` … `rows22325R_431` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29059 tests: row 120 columns 48–54, row 120 columns 55–62, row 120 columns
63–299, row 121 columns 0–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_428 : rowsJ2 120 121 48 55 ≤ 85156767317077 := by decide +kernel

theorem rows22325R_429 : rowsJ2 120 121 55 63 ≤ 41233516852781 := by decide +kernel

theorem rows22325R_430 : rowsJ2 120 121 63 300 ≤ 501580187721367 := by decide +kernel

theorem rows22325R_431 : rowsJ2 121 122 0 48 ≤ 186750023619627 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_428
#print axioms SieveCert.rows22325R_431
