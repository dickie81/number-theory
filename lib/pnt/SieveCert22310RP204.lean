/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 814–817 of 1732

File 204 of 430: the parts `rows22310R_814` … `rows22310R_817` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27048 tests: row 122 columns 100–102, row 122 columns 103–105, row 122
columns 106–108, row 122 columns 109–111), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22310R_814 : rowsJ2 122 123 100 103 ≤ 501902723534 := by decide +kernel

theorem rows22310R_815 : rowsJ2 122 123 103 106 ≤ 2549485383602 := by decide +kernel

theorem rows22310R_816 : rowsJ2 122 123 106 109 ≤ 5621836428787 := by decide +kernel

theorem rows22310R_817 : rowsJ2 122 123 109 112 ≤ 9813597299906 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_814
#print axioms SieveCert.rows22310R_817
