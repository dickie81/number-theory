/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 434–437 of 561

File 113 of 143: the parts `rows22322R_434` … `rows22322R_437` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27108 tests: row 121 columns 63–299, row 122 columns 0–46, row 122 columns
47–53, row 122 columns 54–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_434 : rowsJ2 121 122 63 300 ≤ 693256897139791 := by decide +kernel

theorem rows22322R_435 : rowsJ2 122 123 0 47 ≤ 171403256384057 := by decide +kernel

theorem rows22322R_436 : rowsJ2 122 123 47 54 ≤ 90725838793605 := by decide +kernel

theorem rows22322R_437 : rowsJ2 122 123 54 62 ≤ 43783492045473 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_434
#print axioms SieveCert.rows22322R_437
