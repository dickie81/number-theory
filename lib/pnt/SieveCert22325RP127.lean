/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 493–496 of 561

File 127 of 142: the parts `rows22325R_493` … `rows22325R_496` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 30000 tests: row 139 columns 42–299, row 140 columns 0–40, row 140 columns
41–299, row 141 columns 0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_493 : rowsJ2 139 140 42 300 ≤ 2896714438692638 := by decide +kernel

theorem rows22325R_494 : rowsJ2 140 141 0 41 ≤ 133494187101099 := by decide +kernel

theorem rows22325R_495 : rowsJ2 140 141 41 300 ≤ 2910006103131614 := by decide +kernel

theorem rows22325R_496 : rowsJ2 141 142 0 41 ≤ 144864728126793 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_493
#print axioms SieveCert.rows22325R_496
