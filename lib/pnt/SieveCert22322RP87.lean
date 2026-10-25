/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 333–336 of 561

File 87 of 143: the parts `rows22322R_333` … `rows22322R_336` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28446 tests: row 102 columns 59–63, row 102 columns 64–69, row 102 columns
70–76, row 102 columns 77–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_333 : rowsJ2 102 103 59 64 ≤ 0 := by decide +kernel

theorem rows22322R_334 : rowsJ2 102 103 64 70 ≤ 0 := by decide +kernel

theorem rows22322R_335 : rowsJ2 102 103 70 77 ≤ 989836195451 := by decide +kernel

theorem rows22322R_336 : rowsJ2 102 103 77 300 ≤ 720847253324271 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_333
#print axioms SieveCert.rows22322R_336
