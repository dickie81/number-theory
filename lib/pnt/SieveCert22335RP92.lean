/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 354–356 of 549

File 92 of 140: the parts `rows22335R_354` … `rows22335R_356` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22921 tests: row 107 columns 0–51, row 107 columns 52–57, row 107 columns
58–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_354 : rowsJ2 107 108 0 52 ≤ 355933288677111 := by decide +kernel

theorem rows22335R_355 : rowsJ2 107 108 52 58 ≤ 28403626825275 := by decide +kernel

theorem rows22335R_356 : rowsJ2 107 108 58 64 ≤ 9549635293405 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_354
#print axioms SieveCert.rows22335R_356
