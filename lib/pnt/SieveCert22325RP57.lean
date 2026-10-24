/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 217–220 of 561

File 57 of 142: the parts `rows22325R_217` … `rows22325R_220` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 28173 tests: row 86 columns 40–61, row 86 columns 62–66, row 86 columns
67–70, row 86 columns 71–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_217 : rowsJ2 86 87 40 62 ≤ 206162236616366 := by decide +kernel

theorem rows22325R_218 : rowsJ2 86 87 62 67 ≤ 1571056705176 := by decide +kernel

theorem rows22325R_219 : rowsJ2 86 87 67 71 ≤ 6355965559752 := by decide +kernel

theorem rows22325R_220 : rowsJ2 86 87 71 75 ≤ 4411544221619 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_217
#print axioms SieveCert.rows22325R_220
