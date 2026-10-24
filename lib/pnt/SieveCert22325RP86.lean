/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 330–332 of 561

File 86 of 142: the parts `rows22325R_330` … `rows22325R_332` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (3 parts, 22725 tests: row 101 columns 75–299, row 102 columns 0–52, row 102 columns
53–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22325R_330 : rowsJ2 101 102 75 300 ≤ 842325729768152 := by decide +kernel

theorem rows22325R_331 : rowsJ2 102 103 0 53 ≤ 441709701973266 := by decide +kernel

theorem rows22325R_332 : rowsJ2 102 103 53 59 ≤ 7519158956499 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_330
#print axioms SieveCert.rows22325R_332
