/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 287–292 of 4715

File 24 of 351: the parts `rows22250R_287` … `rows22250R_292` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 95985 tests: row 40 columns 31–31, row 40 columns 32–32, row 40 columns
33–33, row 40 columns 34–34, row 40 columns 35–35, row 40 columns 36–36), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22250R_287 : rowsJ2 40 41 31 32 ≤ 469491668498 := by decide +kernel

theorem rows22250R_288 : rowsJ2 40 41 32 33 ≤ 478361084900 := by decide +kernel

theorem rows22250R_289 : rowsJ2 40 41 33 34 ≤ 458389076476 := by decide +kernel

theorem rows22250R_290 : rowsJ2 40 41 34 35 ≤ 431615188164 := by decide +kernel

theorem rows22250R_291 : rowsJ2 40 41 35 36 ≤ 387977725971 := by decide +kernel

theorem rows22250R_292 : rowsJ2 40 41 36 37 ≤ 348044566479 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_287
#print axioms SieveCert.rows22250R_292
