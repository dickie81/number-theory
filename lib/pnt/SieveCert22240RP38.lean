/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 404–409 of 5066

File 38 of 387: the parts `rows22240R_404` … `rows22240R_409` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 97604 in units of a depth-4 test: row 44 columns 38–38, row 44 columns
39–39, row 44 columns 40–40, row 44 columns 41–41, row 44 columns 42–42, row 44 columns 43–43), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_404 : rowsJ2 44 45 38 39 ≤ 177591910181 := by decide +kernel

theorem rows22240R_405 : rowsJ2 44 45 39 40 ≤ 145552813328 := by decide +kernel

theorem rows22240R_406 : rowsJ2 44 45 40 41 ≤ 121185243303 := by decide +kernel

theorem rows22240R_407 : rowsJ2 44 45 41 42 ≤ 94830751881 := by decide +kernel

theorem rows22240R_408 : rowsJ2 44 45 42 43 ≤ 76159580340 := by decide +kernel

theorem rows22240R_409 : rowsJ2 44 45 43 44 ≤ 55428457406 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_404
#print axioms SieveCert.rows22240R_409
