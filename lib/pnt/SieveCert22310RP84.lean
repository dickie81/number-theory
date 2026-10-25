/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 337–340 of 1732

File 84 of 430: the parts `rows22310R_337` … `rows22310R_340` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29314 tests: row 90 columns 44–49, row 90 columns 50–54, row 90 columns
55–61, row 90 columns 62–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_337 : rowsJ2 90 91 44 50 ≤ 119266604776684 := by decide +kernel

theorem rows22310R_338 : rowsJ2 90 91 50 55 ≤ 177990986228312 := by decide +kernel

theorem rows22310R_339 : rowsJ2 90 91 55 62 ≤ 230049453504040 := by decide +kernel

theorem rows22310R_340 : rowsJ2 90 91 62 72 ≤ 251745158104151 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_337
#print axioms SieveCert.rows22310R_340
