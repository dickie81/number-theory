/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 297–300 of 1732

File 74 of 430: the parts `rows22310R_297` … `rows22310R_300` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29150 tests: row 85 columns 44–49, row 85 columns 50–54, row 85 columns
55–59, row 85 columns 60–66), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_297 : rowsJ2 85 86 44 50 ≤ 92154355172198 := by decide +kernel

theorem rows22310R_298 : rowsJ2 85 86 50 55 ≤ 156501870323496 := by decide +kernel

theorem rows22310R_299 : rowsJ2 85 86 55 60 ≤ 189330896651838 := by decide +kernel

theorem rows22310R_300 : rowsJ2 85 86 60 67 ≤ 228332797133236 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_297
#print axioms SieveCert.rows22310R_300
