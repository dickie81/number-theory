/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 484–488 of 561

File 125 of 142: the parts `rows22325R_484` … `rows22325R_488` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 26027 tests: row 136 columns 43–52, row 136 columns 53–299, row 137 columns
0–41, row 137 columns 42–51, row 137 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_484 : rowsJ2 136 137 43 53 ≤ 119383809793383 := by decide +kernel

theorem rows22325R_485 : rowsJ2 136 137 53 300 ≤ 2795244537055415 := by decide +kernel

theorem rows22325R_486 : rowsJ2 137 138 0 42 ≤ 125668308323810 := by decide +kernel

theorem rows22325R_487 : rowsJ2 137 138 42 52 ≤ 128506889770880 := by decide +kernel

theorem rows22325R_488 : rowsJ2 137 138 52 300 ≤ 2795574423490741 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_484
#print axioms SieveCert.rows22325R_488
