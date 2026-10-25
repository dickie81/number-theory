/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 261–263 of 561

File 68 of 143: the parts `rows22322R_261` … `rows22322R_263` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 23462 tests: row 91 columns 75–80, row 91 columns 81–299, row 92 columns
0–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_261 : rowsJ2 91 92 75 81 ≤ 8672893595942 := by decide +kernel

theorem rows22322R_262 : rowsJ2 91 92 81 300 ≤ 629867175720068 := by decide +kernel

theorem rows22322R_263 : rowsJ2 92 93 0 53 ≤ 675629358108848 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_261
#print axioms SieveCert.rows22322R_263
