/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 401–405 of 5796

File 38 of 465: the parts `rows22250R_401` … `rows22250R_405` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 96308 tests: row 44 columns 39–39, row 44 columns 40–40, row 44 columns
41–41, row 44 columns 42–42, row 44 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_401 : rowsJ2 44 45 39 40 ≤ 160374356682 := by decide +kernel

theorem rows22250R_402 : rowsJ2 44 45 40 41 ≤ 136136586712 := by decide +kernel

theorem rows22250R_403 : rowsJ2 44 45 41 42 ≤ 109797018704 := by decide +kernel

theorem rows22250R_404 : rowsJ2 44 45 42 43 ≤ 92528364612 := by decide +kernel

theorem rows22250R_405 : rowsJ2 44 45 43 44 ≤ 73073482979 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_401
#print axioms SieveCert.rows22250R_405
