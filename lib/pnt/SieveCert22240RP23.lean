/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 289–292 of 5066

File 23 of 387: the parts `rows22240R_289` … `rows22240R_292` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (4 parts, work 81196 in units of a depth-4 test: row 39 columns 35–35, row 39 columns
36–36, row 39 columns 37–37, row 39 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22240R_289 : rowsJ2 39 40 35 36 ≤ 682561613177 := by decide +kernel

theorem rows22240R_290 : rowsJ2 39 40 36 37 ≤ 643417015098 := by decide +kernel

theorem rows22240R_291 : rowsJ2 39 40 37 38 ≤ 595807614873 := by decide +kernel

theorem rows22240R_292 : rowsJ2 39 40 38 39 ≤ 537894292175 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_289
#print axioms SieveCert.rows22240R_292
