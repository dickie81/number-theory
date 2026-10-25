/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 503–506 of 1732

File 127 of 430: the parts `rows22310R_503` … `rows22310R_506` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27283 tests: row 105 columns 90–92, row 105 columns 93–94, row 105 columns
95–96, row 105 columns 97–98), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_503 : rowsJ2 105 106 90 93 ≤ 2891845978668 := by decide +kernel

theorem rows22310R_504 : rowsJ2 105 106 93 95 ≤ 3409875723898 := by decide +kernel

theorem rows22310R_505 : rowsJ2 105 106 95 97 ≤ 4915442614632 := by decide +kernel

theorem rows22310R_506 : rowsJ2 105 106 97 99 ≤ 5504324150426 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_503
#print axioms SieveCert.rows22310R_506
