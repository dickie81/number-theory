/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 970–973 of 1732

File 243 of 430: the parts `rows22310R_970` … `rows22310R_973` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26382 tests: row 131 columns 103–106, row 131 columns 107–110, row 131
columns 111–399, row 132 columns 0–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_970 : rowsJ2 131 132 103 107 ≤ 6711256784484 := by decide +kernel

theorem rows22310R_971 : rowsJ2 131 132 107 111 ≤ 15790940521264 := by decide +kernel

theorem rows22310R_972 : rowsJ2 131 132 111 400 ≤ 813793445613885 := by decide +kernel

theorem rows22310R_973 : rowsJ2 132 133 0 36 ≤ 181820885818760 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_970
#print axioms SieveCert.rows22310R_973
