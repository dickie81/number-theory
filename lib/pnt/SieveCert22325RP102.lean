/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 392–395 of 561

File 102 of 142: the parts `rows22325R_392` … `rows22325R_395` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27154 tests: row 112 columns 70–299, row 113 columns 0–49, row 113 columns
50–55, row 113 columns 56–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_392 : rowsJ2 112 113 70 300 ≤ 216262065218724 := by decide +kernel

theorem rows22325R_393 : rowsJ2 113 114 0 50 ≤ 267201951043367 := by decide +kernel

theorem rows22325R_394 : rowsJ2 113 114 50 56 ≤ 52610415915250 := by decide +kernel

theorem rows22325R_395 : rowsJ2 113 114 56 62 ≤ 32931535629413 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_392
#print axioms SieveCert.rows22325R_395
