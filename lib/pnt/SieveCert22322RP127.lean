/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 492–494 of 561

File 127 of 143: the parts `rows22322R_492` … `rows22322R_494` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22670 tests: row 139 columns 0–41, row 139 columns 42–299, row 140 columns
0–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_492 : rowsJ2 139 140 0 42 ≤ 144898123884308 := by decide +kernel

theorem rows22322R_493 : rowsJ2 139 140 42 300 ≤ 2973878506806532 := by decide +kernel

theorem rows22322R_494 : rowsJ2 140 141 0 41 ≤ 133920845976220 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_492
#print axioms SieveCert.rows22322R_494
