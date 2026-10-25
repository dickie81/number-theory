/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 614–617 of 1732

File 155 of 430: the parts `rows22310R_614` … `rows22310R_617` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29328 tests: row 112 columns 45–60, row 112 columns 61–78, row 112 columns
79–83, row 112 columns 84–86), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_614 : rowsJ2 112 113 45 61 ≤ 307070441593529 := by decide +kernel

theorem rows22310R_615 : rowsJ2 112 113 61 79 ≤ 112177895519002 := by decide +kernel

theorem rows22310R_616 : rowsJ2 112 113 79 84 ≤ 2035887090274 := by decide +kernel

theorem rows22310R_617 : rowsJ2 112 113 84 87 ≤ 122957222990 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_614
#print axioms SieveCert.rows22310R_617
