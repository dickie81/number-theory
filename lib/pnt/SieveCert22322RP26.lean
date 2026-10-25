/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 101–103 of 561

File 26 of 143: the parts `rows22322R_101` … `rows22322R_103` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22847 tests: row 64 columns 0–34, row 64 columns 35–44, row 64 columns
45–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_101 : rowsJ2 64 65 0 35 ≤ 804495604786497 := by decide +kernel

theorem rows22322R_102 : rowsJ2 64 65 35 45 ≤ 587909688010421 := by decide +kernel

theorem rows22322R_103 : rowsJ2 64 65 45 300 ≤ 798591032815178 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_101
#print axioms SieveCert.rows22322R_103
