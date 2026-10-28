/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 399–403 of 5066

File 37 of 387: the parts `rows22240R_399` … `rows22240R_403` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (5 parts, work 85843 in units of a depth-4 test: row 44 columns 33–33, row 44 columns
34–34, row 44 columns 35–35, row 44 columns 36–36, row 44 columns 37–37), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22240R_399 : rowsJ2 44 45 33 34 ≤ 354035731076 := by decide +kernel

theorem rows22240R_400 : rowsJ2 44 45 34 35 ≤ 324934063105 := by decide +kernel

theorem rows22240R_401 : rowsJ2 44 45 35 36 ≤ 281947291834 := by decide +kernel

theorem rows22240R_402 : rowsJ2 44 45 36 37 ≤ 247703619470 := by decide +kernel

theorem rows22240R_403 : rowsJ2 44 45 37 38 ≤ 207010342911 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_399
#print axioms SieveCert.rows22240R_403
