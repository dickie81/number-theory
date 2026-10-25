/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 457–460 of 1732

File 115 of 430: the parts `rows22310R_457` … `rows22310R_460` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28871 tests: row 102 columns 44–50, row 102 columns 51–61, row 102 columns
62–80, row 102 columns 81–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_457 : rowsJ2 102 103 44 51 ≤ 216654052270309 := by decide +kernel

theorem rows22310R_458 : rowsJ2 102 103 51 62 ≤ 268141275600538 := by decide +kernel

theorem rows22310R_459 : rowsJ2 102 103 62 81 ≤ 227295012679941 := by decide +kernel

theorem rows22310R_460 : rowsJ2 102 103 81 86 ≤ 19235439253943 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_457
#print axioms SieveCert.rows22310R_460
