/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 749–752 of 1732

File 188 of 430: the parts `rows22310R_749` … `rows22310R_752` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24728 tests: row 119 columns 83–85, row 119 columns 86–87, row 119 columns
88–89, row 119 columns 90–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_749 : rowsJ2 119 120 83 86 ≤ 29628096959 := by decide +kernel

theorem rows22310R_750 : rowsJ2 119 120 86 88 ≤ 272557598274 := by decide +kernel

theorem rows22310R_751 : rowsJ2 119 120 88 90 ≤ 770750405727 := by decide +kernel

theorem rows22310R_752 : rowsJ2 119 120 90 92 ≤ 992463381574 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_749
#print axioms SieveCert.rows22310R_752
