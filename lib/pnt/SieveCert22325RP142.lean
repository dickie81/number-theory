/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 560–560 of 561

File 142 of 142: the parts `rows22325R_560` … `rows22325R_560` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (1 parts, 4056 tests: rows 297–299), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_560 : rows2 297 300 ≤ 43543218378479716 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_560
