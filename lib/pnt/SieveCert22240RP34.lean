/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 376–380 of 5066

File 34 of 387: the parts `rows22240R_376` … `rows22240R_380` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (5 parts, work 89956 in units of a depth-4 test: row 43 columns 34–34, row 43 columns
35–35, row 43 columns 36–36, row 43 columns 37–37, row 43 columns 38–38), each a sum of refined costs (`rows2` or
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

theorem rows22240R_376 : rowsJ2 43 44 34 35 ≤ 381642572736 := by decide +kernel

theorem rows22240R_377 : rowsJ2 43 44 35 36 ≤ 343431204623 := by decide +kernel

theorem rows22240R_378 : rowsJ2 43 44 36 37 ≤ 298583031659 := by decide +kernel

theorem rows22240R_379 : rowsJ2 43 44 37 38 ≤ 258911283560 := by decide +kernel

theorem rows22240R_380 : rowsJ2 43 44 38 39 ≤ 218303233523 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_376
#print axioms SieveCert.rows22240R_380
