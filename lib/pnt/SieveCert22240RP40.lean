/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 422–427 of 5066

File 40 of 387: the parts `rows22240R_422` … `rows22240R_427` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 94661 in units of a depth-4 test: row 45 columns 31–31, row 45 columns
32–32, row 45 columns 33–33, row 45 columns 34–34, row 45 columns 35–35, row 45 columns 36–36), each a sum of
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

theorem rows22240R_422 : rowsJ2 45 46 31 32 ≤ 351076836566 := by decide +kernel

theorem rows22240R_423 : rowsJ2 45 46 32 33 ≤ 327024688044 := by decide +kernel

theorem rows22240R_424 : rowsJ2 45 46 33 34 ≤ 301342971205 := by decide +kernel

theorem rows22240R_425 : rowsJ2 45 46 34 35 ≤ 264907674161 := by decide +kernel

theorem rows22240R_426 : rowsJ2 45 46 35 36 ≤ 232526535653 := by decide +kernel

theorem rows22240R_427 : rowsJ2 45 46 36 37 ≤ 195904340823 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_422
#print axioms SieveCert.rows22240R_427
