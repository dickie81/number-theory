/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 364–367 of 561

File 95 of 143: the parts `rows22322R_364` … `rows22322R_367` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24201 tests: row 107 columns 63–68, row 107 columns 69–76, row 107 columns
77–299, row 108 columns 0–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_364 : rowsJ2 107 108 63 69 ≤ 0 := by decide +kernel

theorem rows22322R_365 : rowsJ2 107 108 69 77 ≤ 1404749289895 := by decide +kernel

theorem rows22322R_366 : rowsJ2 107 108 77 300 ≤ 453549681736942 := by decide +kernel

theorem rows22322R_367 : rowsJ2 108 109 0 51 ≤ 337300985214318 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_364
#print axioms SieveCert.rows22322R_367
