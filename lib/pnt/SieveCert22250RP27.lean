/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 310–314 of 4715

File 27 of 351: the parts `rows22250R_310` … `rows22250R_314` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 84406 tests: row 41 columns 34–34, row 41 columns 35–35, row 41 columns
36–36, row 41 columns 37–37, row 41 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_310 : rowsJ2 41 42 34 35 ≤ 353572556460 := by decide +kernel

theorem rows22250R_311 : rowsJ2 41 42 35 36 ≤ 315627476171 := by decide +kernel

theorem rows22250R_312 : rowsJ2 41 42 36 37 ≤ 273866758255 := by decide +kernel

theorem rows22250R_313 : rowsJ2 41 42 37 38 ≤ 236735112461 := by decide +kernel

theorem rows22250R_314 : rowsJ2 41 42 38 39 ≤ 201582105167 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_310
#print axioms SieveCert.rows22250R_314
