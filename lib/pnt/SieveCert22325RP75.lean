/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 287–290 of 561

File 75 of 142: the parts `rows22325R_287` … `rows22325R_290` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 25464 tests: row 95 columns 66–70, row 95 columns 71–76, row 95 columns
77–83, row 95 columns 84–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_287 : rowsJ2 95 96 66 71 ≤ 22632158219 := by decide +kernel

theorem rows22325R_288 : rowsJ2 95 96 71 77 ≤ 620287911344 := by decide +kernel

theorem rows22325R_289 : rowsJ2 95 96 77 84 ≤ 32476951940408 := by decide +kernel

theorem rows22325R_290 : rowsJ2 95 96 84 300 ≤ 1280865987308628 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_287
#print axioms SieveCert.rows22325R_290
