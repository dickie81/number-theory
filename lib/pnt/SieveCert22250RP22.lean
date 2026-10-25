/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 270–274 of 4715

File 22 of 351: the parts `rows22250R_270` … `rows22250R_274` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 89816 tests: row 39 columns 34–34, row 39 columns 35–35, row 39 columns
36–36, row 39 columns 37–37, row 39 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22250R_270 : rowsJ2 39 40 34 35 ≤ 509952685327 := by decide +kernel

theorem rows22250R_271 : rowsJ2 39 40 35 36 ≤ 469484250416 := by decide +kernel

theorem rows22250R_272 : rowsJ2 39 40 36 37 ≤ 423859048445 := by decide +kernel

theorem rows22250R_273 : rowsJ2 39 40 37 38 ≤ 375983297699 := by decide +kernel

theorem rows22250R_274 : rowsJ2 39 40 38 39 ≤ 327895945392 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_270
#print axioms SieveCert.rows22250R_274
