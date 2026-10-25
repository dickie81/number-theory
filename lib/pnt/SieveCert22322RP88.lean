/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 337–339 of 561

File 88 of 143: the parts `rows22322R_337` … `rows22322R_339` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22432 tests: row 103 columns 0–51, row 103 columns 52–58, row 103 columns
59–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_337 : rowsJ2 103 104 0 52 ≤ 423815923878044 := by decide +kernel

theorem rows22322R_338 : rowsJ2 103 104 52 59 ≤ 13824205149774 := by decide +kernel

theorem rows22322R_339 : rowsJ2 103 104 59 64 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_337
#print axioms SieveCert.rows22322R_339
