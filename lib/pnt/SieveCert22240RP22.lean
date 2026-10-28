/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 282–288 of 5066

File 22 of 387: the parts `rows22240R_282` … `rows22240R_288` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 84026 in units of a depth-4 test: row 39 columns 28–28, row 39 columns
29–29, row 39 columns 30–30, row 39 columns 31–31, row 39 columns 32–32, row 39 columns 33–33, row 39 columns
34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

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

theorem rows22240R_282 : rowsJ2 39 40 28 29 ≤ 713272680283 := by decide +kernel

theorem rows22240R_283 : rowsJ2 39 40 29 30 ≤ 670680782464 := by decide +kernel

theorem rows22240R_284 : rowsJ2 39 40 30 31 ≤ 643451262374 := by decide +kernel

theorem rows22240R_285 : rowsJ2 39 40 31 32 ≤ 638232775471 := by decide +kernel

theorem rows22240R_286 : rowsJ2 39 40 32 33 ≤ 669174523032 := by decide +kernel

theorem rows22240R_287 : rowsJ2 39 40 33 34 ≤ 701864307777 := by decide +kernel

theorem rows22240R_288 : rowsJ2 39 40 34 35 ≤ 700535595443 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_282
#print axioms SieveCert.rows22240R_288
