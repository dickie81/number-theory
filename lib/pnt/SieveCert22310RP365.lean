/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1452–1455 of 1732

File 365 of 430: the parts `rows22310R_1452` … `rows22310R_1455` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28784 tests: row 173 columns 59–62, row 173 columns 63–66, row 173 columns
67–71, row 173 columns 72–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1452 : rowsJ2 173 174 59 63 ≤ 33880112724377 := by decide +kernel

theorem rows22310R_1453 : rowsJ2 173 174 63 67 ≤ 32862548111179 := by decide +kernel

theorem rows22310R_1454 : rowsJ2 173 174 67 72 ≤ 25344571525939 := by decide +kernel

theorem rows22310R_1455 : rowsJ2 173 174 72 77 ≤ 12525927708281 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1452
#print axioms SieveCert.rows22310R_1455
