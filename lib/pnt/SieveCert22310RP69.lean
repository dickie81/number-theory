/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 277–280 of 1732

File 69 of 430: the parts `rows22310R_277` … `rows22310R_280` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28644 tests: row 82 columns 66–73, row 82 columns 74–399, row 83 columns
0–34, row 83 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_277 : rowsJ2 82 83 66 74 ≤ 235312483549716 := by decide +kernel

theorem rows22310R_278 : rowsJ2 82 83 74 400 ≤ 198011932432076 := by decide +kernel

theorem rows22310R_279 : rowsJ2 83 84 0 35 ≤ 636489725030798 := by decide +kernel

theorem rows22310R_280 : rowsJ2 83 84 35 44 ≤ 80334484333962 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_277
#print axioms SieveCert.rows22310R_280
