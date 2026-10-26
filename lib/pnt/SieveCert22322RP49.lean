/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 187–189 of 561

File 49 of 143: the parts `rows22322R_187` … `rows22322R_189` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 23062 tests: row 82 columns 0–36, row 82 columns 37–61, row 82 columns
62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_187 : rowsJ2 82 83 0 37 ≤ 613264299020614 := by decide +kernel

theorem rows22322R_188 : rowsJ2 82 83 37 62 ≤ 441136732054343 := by decide +kernel

theorem rows22322R_189 : rowsJ2 82 83 62 68 ≤ 2974523499939 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_187
#print axioms SieveCert.rows22322R_189
