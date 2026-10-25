/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 307–309 of 561

File 80 of 143: the parts `rows22322R_307` … `rows22322R_309` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22299 tests: row 98 columns 60–64, row 98 columns 65–69, row 98 columns
70–75), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_307 : rowsJ2 98 99 60 65 ≤ 0 := by decide +kernel

theorem rows22322R_308 : rowsJ2 98 99 65 70 ≤ 0 := by decide +kernel

theorem rows22322R_309 : rowsJ2 98 99 70 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_307
#print axioms SieveCert.rows22322R_309
