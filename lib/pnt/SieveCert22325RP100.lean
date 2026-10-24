/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 384–387 of 561

File 100 of 142: the parts `rows22325R_384` … `rows22325R_387` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28025 tests: row 111 columns 51–56, row 111 columns 57–62, row 111 columns
63–70, row 111 columns 71–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_384 : rowsJ2 111 112 51 57 ≤ 45189267912525 := by decide +kernel

theorem rows22325R_385 : rowsJ2 111 112 57 63 ≤ 25068835235726 := by decide +kernel

theorem rows22325R_386 : rowsJ2 111 112 63 71 ≤ 3775144566224 := by decide +kernel

theorem rows22325R_387 : rowsJ2 111 112 71 300 ≤ 218807125616816 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_384
#print axioms SieveCert.rows22325R_387
