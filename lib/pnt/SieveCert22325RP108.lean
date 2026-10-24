/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 416–419 of 561

File 108 of 142: the parts `rows22325R_416` … `rows22325R_419` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24020 tests: row 117 columns 62–71, row 117 columns 72–299, row 118 columns
0–48, row 118 columns 49–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_416 : rowsJ2 117 118 62 72 ≤ 9497501405567 := by decide +kernel

theorem rows22325R_417 : rowsJ2 117 118 72 300 ≤ 0 := by decide +kernel

theorem rows22325R_418 : rowsJ2 118 119 0 49 ≤ 213606194726193 := by decide +kernel

theorem rows22325R_419 : rowsJ2 118 119 49 55 ≤ 69819726113249 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_416
#print axioms SieveCert.rows22325R_419
