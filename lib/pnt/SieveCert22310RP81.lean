/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 325–328 of 1732

File 81 of 430: the parts `rows22310R_325` … `rows22310R_328` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27427 tests: row 88 columns 69–83, row 88 columns 84–399, row 89 columns
0–34, row 89 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_325 : rowsJ2 88 89 69 84 ≤ 281481450654574 := by decide +kernel

theorem rows22310R_326 : rowsJ2 88 89 84 400 ≤ 55341744350244 := by decide +kernel

theorem rows22310R_327 : rowsJ2 89 90 0 35 ≤ 484398416431235 := by decide +kernel

theorem rows22310R_328 : rowsJ2 89 90 35 44 ≤ 57231647018052 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_325
#print axioms SieveCert.rows22310R_328
