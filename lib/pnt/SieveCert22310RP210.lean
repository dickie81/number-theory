/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 839–842 of 1732

File 210 of 430: the parts `rows22310R_839` … `rows22310R_842` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28479 tests: row 124 columns 35–57, row 124 columns 58–74, row 124 columns
75–78, row 124 columns 79–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_839 : rowsJ2 124 125 35 58 ≤ 351949871701724 := by decide +kernel

theorem rows22310R_840 : rowsJ2 124 125 58 75 ≤ 33511438050665 := by decide +kernel

theorem rows22310R_841 : rowsJ2 124 125 75 79 ≤ 0 := by decide +kernel

theorem rows22310R_842 : rowsJ2 124 125 79 82 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_839
#print axioms SieveCert.rows22310R_842
