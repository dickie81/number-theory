/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 542–545 of 1732

File 137 of 430: the parts `rows22310R_542` … `rows22310R_545` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28621 tests: row 107 columns 106–399, row 108 columns 0–34, row 108 columns
35–43, row 108 columns 44–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_542 : rowsJ2 107 108 106 400 ≤ 3352014590170 := by decide +kernel

theorem rows22310R_543 : rowsJ2 108 109 0 35 ≤ 136221240777214 := by decide +kernel

theorem rows22310R_544 : rowsJ2 108 109 35 44 ≤ 168413804932560 := by decide +kernel

theorem rows22310R_545 : rowsJ2 108 109 44 54 ≤ 261971835256936 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_542
#print axioms SieveCert.rows22310R_545
