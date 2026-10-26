/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 410–413 of 561

File 107 of 143: the parts `rows22322R_410` … `rows22322R_413` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25509 tests: row 116 columns 55–61, row 116 columns 62–70, row 116 columns
71–299, row 117 columns 0–48), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_410 : rowsJ2 116 117 55 62 ≤ 43503729516823 := by decide +kernel

theorem rows22322R_411 : rowsJ2 116 117 62 71 ≤ 10218270292572 := by decide +kernel

theorem rows22322R_412 : rowsJ2 116 117 71 300 ≤ 0 := by decide +kernel

theorem rows22322R_413 : rowsJ2 117 118 0 49 ≤ 222516202793936 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_410
#print axioms SieveCert.rows22322R_413
