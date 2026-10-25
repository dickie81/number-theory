/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 209–212 of 1732

File 52 of 430: the parts `rows22310R_209` … `rows22310R_212` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28220 tests: row 75 columns 35–43, row 75 columns 44–49, row 75 columns
50–54, row 75 columns 55–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_209 : rowsJ2 75 76 35 44 ≤ 157561377220585 := by decide +kernel

theorem rows22310R_210 : rowsJ2 75 76 44 50 ≤ 86258344041342 := by decide +kernel

theorem rows22310R_211 : rowsJ2 75 76 50 55 ≤ 108848626524075 := by decide +kernel

theorem rows22310R_212 : rowsJ2 75 76 55 59 ≤ 134910997348956 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_209
#print axioms SieveCert.rows22310R_212
