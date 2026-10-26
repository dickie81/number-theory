/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 560–560 of 561

File 143 of 143: the parts `rows22322R_560` … `rows22322R_560` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (1 parts, 4056 tests: rows 297–299), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_560 : rows2 297 300 ≤ 43589720054550639 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_560
