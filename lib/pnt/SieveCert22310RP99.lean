/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 395–398 of 1732

File 99 of 430: the parts `rows22310R_395` … `rows22310R_398` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27980 tests: row 96 columns 92–94, row 96 columns 95–399, row 97 columns
0–34, row 97 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_395 : rowsJ2 96 97 92 95 ≤ 10361655583720 := by decide +kernel

theorem rows22310R_396 : rowsJ2 96 97 95 400 ≤ 6815668590567 := by decide +kernel

theorem rows22310R_397 : rowsJ2 97 98 0 35 ≤ 301374090133193 := by decide +kernel

theorem rows22310R_398 : rowsJ2 97 98 35 44 ≤ 77930644919104 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_395
#print axioms SieveCert.rows22310R_398
