/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 753–756 of 1732

File 189 of 430: the parts `rows22310R_753` … `rows22310R_756` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 22816 tests: row 119 columns 92–93, row 119 columns 94–95, row 119 columns
96–97, row 119 columns 98–99), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_753 : rowsJ2 119 120 92 94 ≤ 778833157702 := by decide +kernel

theorem rows22310R_754 : rowsJ2 119 120 94 96 ≤ 587671115066 := by decide +kernel

theorem rows22310R_755 : rowsJ2 119 120 96 98 ≤ 419720105964 := by decide +kernel

theorem rows22310R_756 : rowsJ2 119 120 98 100 ≤ 278383846401 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_753
#print axioms SieveCert.rows22310R_756
