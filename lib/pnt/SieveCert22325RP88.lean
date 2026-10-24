/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 337–339 of 561

File 88 of 142: the parts `rows22325R_337` … `rows22325R_339` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22432 tests: row 103 columns 0–51, row 103 columns 52–58, row 103 columns
59–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_337 : rowsJ2 103 104 0 52 ≤ 422102788610049 := by decide +kernel

theorem rows22325R_338 : rowsJ2 103 104 52 59 ≤ 13787101679680 := by decide +kernel

theorem rows22325R_339 : rowsJ2 103 104 59 64 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_337
#print axioms SieveCert.rows22325R_339
