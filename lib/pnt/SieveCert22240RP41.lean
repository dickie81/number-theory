/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 428–433 of 5066

File 41 of 387: the parts `rows22240R_428` … `rows22240R_433` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 96017 in units of a depth-4 test: row 45 columns 37–37, row 45 columns
38–38, row 45 columns 39–39, row 45 columns 40–40, row 45 columns 41–41, row 45 columns 42–42), each a sum of
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

theorem rows22240R_428 : rowsJ2 45 46 37 38 ≤ 166413552144 := by decide +kernel

theorem rows22240R_429 : rowsJ2 45 46 38 39 ≤ 137166130653 := by decide +kernel

theorem rows22240R_430 : rowsJ2 45 46 39 40 ≤ 112747005044 := by decide +kernel

theorem rows22240R_431 : rowsJ2 45 46 40 41 ≤ 88502671852 := by decide +kernel

theorem rows22240R_432 : rowsJ2 45 46 41 42 ≤ 69796647524 := by decide +kernel

theorem rows22240R_433 : rowsJ2 45 46 42 43 ≤ 51204083184 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_428
#print axioms SieveCert.rows22240R_433
