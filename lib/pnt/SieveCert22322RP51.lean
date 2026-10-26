/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 194–197 of 561

File 51 of 143: the parts `rows22322R_194` … `rows22322R_197` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28642 tests: row 83 columns 0–36, row 83 columns 37–61, row 83 columns 62–66,
row 83 columns 67–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_194 : rowsJ2 83 84 0 37 ≤ 607113428078937 := by decide +kernel

theorem rows22322R_195 : rowsJ2 83 84 37 62 ≤ 402252896903485 := by decide +kernel

theorem rows22322R_196 : rowsJ2 83 84 62 67 ≤ 1612848147201 := by decide +kernel

theorem rows22322R_197 : rowsJ2 83 84 67 71 ≤ 8732744579489 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_194
#print axioms SieveCert.rows22322R_197
