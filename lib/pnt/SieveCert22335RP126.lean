/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 488–491 of 549

File 126 of 140: the parts `rows22335R_488` … `rows22335R_491` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25298 tests: row 143 columns 0–40, row 143 columns 41–299, row 144 columns
0–39, row 144 columns 40–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_488 : rowsJ2 143 144 0 41 ≤ 169261440551343 := by decide +kernel

theorem rows22335R_489 : rowsJ2 143 144 41 300 ≤ 2865751816468505 := by decide +kernel

theorem rows22335R_490 : rowsJ2 144 145 0 40 ≤ 160891552816534 := by decide +kernel

theorem rows22335R_491 : rowsJ2 144 145 40 300 ≤ 2875255228864698 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_488
#print axioms SieveCert.rows22335R_491
