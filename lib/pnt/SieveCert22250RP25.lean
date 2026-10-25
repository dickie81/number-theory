/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 293–300 of 4715

File 25 of 351: the parts `rows22250R_293` … `rows22250R_300` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 98346 tests: row 40 columns 37–37, row 40 columns 38–38, row 40 columns
39–39, row 40 columns 40–339, row 41 columns 0–13, row 41 columns 14–17, row 41 columns 18–20, row 41 columns
21–23), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

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

theorem rows22250R_293 : rowsJ2 40 41 37 38 ≤ 300679726426 := by decide +kernel

theorem rows22250R_294 : rowsJ2 40 41 38 39 ≤ 262820499971 := by decide +kernel

theorem rows22250R_295 : rowsJ2 40 41 39 40 ≤ 221814880411 := by decide +kernel

theorem rows22250R_296 : rowsJ2 40 41 40 340 ≤ 187797674765 := by decide +kernel

theorem rows22250R_297 : rowsJ2 41 42 0 14 ≤ 1392118765862 := by decide +kernel

theorem rows22250R_298 : rowsJ2 41 42 14 18 ≤ 3271818528707 := by decide +kernel

theorem rows22250R_299 : rowsJ2 41 42 18 21 ≤ 2613930654018 := by decide +kernel

theorem rows22250R_300 : rowsJ2 41 42 21 24 ≤ 2151348034262 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_293
#print axioms SieveCert.rows22250R_300
