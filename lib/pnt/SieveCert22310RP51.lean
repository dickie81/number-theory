/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 205–208 of 1732

File 51 of 430: the parts `rows22310R_205` … `rows22310R_208` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24694 tests: row 74 columns 63–67, row 74 columns 68–73, row 74 columns
74–399, row 75 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_205 : rowsJ2 74 75 63 68 ≤ 199681522637401 := by decide +kernel

theorem rows22310R_206 : rowsJ2 74 75 68 74 ≤ 212248263340626 := by decide +kernel

theorem rows22310R_207 : rowsJ2 74 75 74 400 ≤ 32401004923639 := by decide +kernel

theorem rows22310R_208 : rowsJ2 75 76 0 35 ≤ 839797940448146 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_205
#print axioms SieveCert.rows22310R_208
