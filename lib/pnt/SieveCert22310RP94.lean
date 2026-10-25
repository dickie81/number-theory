/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 375–378 of 1732

File 94 of 430: the parts `rows22310R_375` … `rows22310R_378` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27881 tests: row 94 columns 82–88, row 94 columns 89–92, row 94 columns
93–399, row 95 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_375 : rowsJ2 94 95 82 89 ≤ 53053434772182 := by decide +kernel

theorem rows22310R_376 : rowsJ2 94 95 89 93 ≤ 20012161938543 := by decide +kernel

theorem rows22310R_377 : rowsJ2 94 95 93 400 ≤ 8686442686500 := by decide +kernel

theorem rows22310R_378 : rowsJ2 95 96 0 35 ≤ 343621725257380 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_375
#print axioms SieveCert.rows22310R_378
