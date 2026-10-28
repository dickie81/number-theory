/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 353–357 of 5066

File 31 of 387: the parts `rows22240R_353` … `rows22240R_357` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (5 parts, work 92536 in units of a depth-4 test: row 42 columns 34–34, row 42 columns
35–35, row 42 columns 36–36, row 42 columns 37–37, row 42 columns 38–38), each a sum of refined costs (`rows2` or
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

theorem rows22240R_353 : rowsJ2 42 43 34 35 ≤ 462515309151 := by decide +kernel

theorem rows22240R_354 : rowsJ2 42 43 35 36 ≤ 420142886885 := by decide +kernel

theorem rows22240R_355 : rowsJ2 42 43 36 37 ≤ 380622099696 := by decide +kernel

theorem rows22240R_356 : rowsJ2 42 43 37 38 ≤ 330087381862 := by decide +kernel

theorem rows22240R_357 : rowsJ2 42 43 38 39 ≤ 290692866339 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_353
#print axioms SieveCert.rows22240R_357
