/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 472–475 of 1732

File 119 of 430: the parts `rows22310R_472` … `rows22310R_475` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28278 tests: row 103 columns 65–81, row 103 columns 82–86, row 103 columns
87–89, row 103 columns 90–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_472 : rowsJ2 103 104 65 82 ≤ 165823772128345 := by decide +kernel

theorem rows22310R_473 : rowsJ2 103 104 82 87 ≤ 14090511808916 := by decide +kernel

theorem rows22310R_474 : rowsJ2 103 104 87 90 ≤ 4030738501946 := by decide +kernel

theorem rows22310R_475 : rowsJ2 103 104 90 93 ≤ 3341888301067 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_472
#print axioms SieveCert.rows22310R_475
