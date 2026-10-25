/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 252–258 of 4715

File 20 of 351: the parts `rows22250R_252` … `rows22250R_258` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 95076 tests: row 38 columns 35–35, row 38 columns 36–36, row 38 columns
37–37, row 38 columns 38–339, row 39 columns 0–13, row 39 columns 14–16, row 39 columns 17–19), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_252 : rowsJ2 38 39 35 36 ≤ 575115797704 := by decide +kernel

theorem rows22250R_253 : rowsJ2 38 39 36 37 ≤ 532836632050 := by decide +kernel

theorem rows22250R_254 : rowsJ2 38 39 37 38 ≤ 478872685461 := by decide +kernel

theorem rows22250R_255 : rowsJ2 38 39 38 340 ≤ 429851008719 := by decide +kernel

theorem rows22250R_256 : rowsJ2 39 40 0 14 ≤ 1145685811913 := by decide +kernel

theorem rows22250R_257 : rowsJ2 39 40 14 17 ≤ 2401112975031 := by decide +kernel

theorem rows22250R_258 : rowsJ2 39 40 17 20 ≤ 2968392368445 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_252
#print axioms SieveCert.rows22250R_258
