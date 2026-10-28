/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 330–334 of 5066

File 28 of 387: the parts `rows22240R_330` … `rows22240R_334` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (5 parts, work 91709 in units of a depth-4 test: row 41 columns 33–33, row 41 columns
34–34, row 41 columns 35–35, row 41 columns 36–36, row 41 columns 37–37), each a sum of refined costs (`rows2` or
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

theorem rows22240R_330 : rowsJ2 41 42 33 34 ≤ 560060263641 := by decide +kernel

theorem rows22240R_331 : rowsJ2 41 42 34 35 ≤ 537984526106 := by decide +kernel

theorem rows22240R_332 : rowsJ2 41 42 35 36 ≤ 507567184382 := by decide +kernel

theorem rows22240R_333 : rowsJ2 41 42 36 37 ≤ 460564454871 := by decide +kernel

theorem rows22240R_334 : rowsJ2 41 42 37 38 ≤ 415307529263 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_330
#print axioms SieveCert.rows22240R_334
