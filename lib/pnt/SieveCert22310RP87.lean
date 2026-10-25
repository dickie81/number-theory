/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 349–352 of 1732

File 87 of 430: the parts `rows22310R_349` … `rows22310R_352` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29233 tests: row 91 columns 75–87, row 91 columns 88–399, row 92 columns
0–34, row 92 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_349 : rowsJ2 91 92 75 88 ≤ 162535058589185 := by decide +kernel

theorem rows22310R_350 : rowsJ2 91 92 88 400 ≤ 28665219205111 := by decide +kernel

theorem rows22310R_351 : rowsJ2 92 93 0 35 ≤ 411804488353035 := by decide +kernel

theorem rows22310R_352 : rowsJ2 92 93 35 44 ≤ 58270892968608 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_349
#print axioms SieveCert.rows22310R_352
