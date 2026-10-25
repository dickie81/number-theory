/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1534–1537 of 1732

File 386 of 430: the parts `rows22310R_1534` … `rows22310R_1537` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29045 tests: row 186 columns 48–53, row 186 columns 54–58, row 186 columns
59–63, row 186 columns 64–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1534 : rowsJ2 186 187 48 54 ≤ 45375500317072 := by decide +kernel

theorem rows22310R_1535 : rowsJ2 186 187 54 59 ≤ 54214090906359 := by decide +kernel

theorem rows22310R_1536 : rowsJ2 186 187 59 64 ≤ 36501446040633 := by decide +kernel

theorem rows22310R_1537 : rowsJ2 186 187 64 400 ≤ 2100717420360167 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1534
#print axioms SieveCert.rows22310R_1537
