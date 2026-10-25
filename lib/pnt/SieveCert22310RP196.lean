/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 782–785 of 1732

File 196 of 430: the parts `rows22310R_782` … `rows22310R_785` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29601 tests: row 121 columns 0–34, row 121 columns 35–49, row 121 columns
50–73, row 121 columns 74–78), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_782 : rowsJ2 121 122 0 35 ≤ 98173996168444 := by decide +kernel

theorem rows22310R_783 : rowsJ2 121 122 35 50 ≤ 309439829959811 := by decide +kernel

theorem rows22310R_784 : rowsJ2 121 122 50 74 ≤ 143849797317653 := by decide +kernel

theorem rows22310R_785 : rowsJ2 121 122 74 79 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_782
#print axioms SieveCert.rows22310R_785
