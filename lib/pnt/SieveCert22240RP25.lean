/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 306–311 of 5066

File 25 of 387: the parts `rows22240R_306` … `rows22240R_311` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 99371 in units of a depth-4 test: row 40 columns 31–31, row 40 columns
32–32, row 40 columns 33–33, row 40 columns 34–34, row 40 columns 35–35, row 40 columns 36–36), each a sum of
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

theorem rows22240R_306 : rowsJ2 40 41 31 32 ≤ 583665984782 := by decide +kernel

theorem rows22240R_307 : rowsJ2 40 41 32 33 ≤ 619443158777 := by decide +kernel

theorem rows22240R_308 : rowsJ2 40 41 33 34 ≤ 625099378144 := by decide +kernel

theorem rows22240R_309 : rowsJ2 40 41 34 35 ≤ 624135179080 := by decide +kernel

theorem rows22240R_310 : rowsJ2 40 41 35 36 ≤ 589681177490 := by decide +kernel

theorem rows22240R_311 : rowsJ2 40 41 36 37 ≤ 554598245697 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_306
#print axioms SieveCert.rows22240R_311
