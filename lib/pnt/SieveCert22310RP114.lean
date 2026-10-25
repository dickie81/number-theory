/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 453–456 of 1732

File 114 of 430: the parts `rows22310R_453` … `rows22310R_456` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25599 tests: row 101 columns 99–100, row 101 columns 101–399, row 102 columns
0–34, row 102 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_453 : rowsJ2 101 102 99 101 ≤ 7586491715961 := by decide +kernel

theorem rows22310R_454 : rowsJ2 101 102 101 400 ≤ 3571471684858 := by decide +kernel

theorem rows22310R_455 : rowsJ2 102 103 0 35 ≤ 210911560041017 := by decide +kernel

theorem rows22310R_456 : rowsJ2 102 103 35 44 ≤ 113185946733653 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_453
#print axioms SieveCert.rows22310R_456
