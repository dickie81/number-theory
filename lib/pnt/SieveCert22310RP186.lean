/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 741–744 of 1732

File 186 of 430: the parts `rows22310R_741` … `rows22310R_744` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26193 tests: row 118 columns 110–112, row 118 columns 113–115, row 118
columns 116–399, row 119 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_741 : rowsJ2 118 119 110 113 ≤ 9315302963772 := by decide +kernel

theorem rows22310R_742 : rowsJ2 118 119 113 116 ≤ 14315171308562 := by decide +kernel

theorem rows22310R_743 : rowsJ2 118 119 116 400 ≤ 20513460447884 := by decide +kernel

theorem rows22310R_744 : rowsJ2 119 120 0 35 ≤ 93129168492414 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_741
#print axioms SieveCert.rows22310R_744
