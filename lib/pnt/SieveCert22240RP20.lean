/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 265–270 of 5066

File 20 of 387: the parts `rows22240R_265` … `rows22240R_270` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 99297 in units of a depth-4 test: row 38 columns 31–31, row 38 columns
32–32, row 38 columns 33–33, row 38 columns 34–34, row 38 columns 35–35, row 38 columns 36–36), each a sum of
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

theorem rows22240R_265 : rowsJ2 38 39 31 32 ≤ 693330226215 := by decide +kernel

theorem rows22240R_266 : rowsJ2 38 39 32 33 ≤ 724781900166 := by decide +kernel

theorem rows22240R_267 : rowsJ2 38 39 33 34 ≤ 772614648706 := by decide +kernel

theorem rows22240R_268 : rowsJ2 38 39 34 35 ≤ 800127913655 := by decide +kernel

theorem rows22240R_269 : rowsJ2 38 39 35 36 ≤ 785409295142 := by decide +kernel

theorem rows22240R_270 : rowsJ2 38 39 36 37 ≤ 763623082759 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_265
#print axioms SieveCert.rows22240R_270
