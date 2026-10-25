/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 379–385 of 5796

File 35 of 465: the parts `rows22250R_379` … `rows22250R_385` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 99846 tests: row 43 columns 40–40, row 43 columns 41–41, row 43 columns
42–42, row 43 columns 43–359, row 44 columns 0–13, row 44 columns 14–16, row 44 columns 17–19), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_379 : rowsJ2 43 44 40 41 ≤ 171821443107 := by decide +kernel

theorem rows22250R_380 : rowsJ2 43 44 41 42 ≤ 145312021878 := by decide +kernel

theorem rows22250R_381 : rowsJ2 43 44 42 43 ≤ 119012942604 := by decide +kernel

theorem rows22250R_382 : rowsJ2 43 44 43 360 ≤ 99447906161 := by decide +kernel

theorem rows22250R_383 : rowsJ2 44 45 0 14 ≤ 824312182630 := by decide +kernel

theorem rows22250R_384 : rowsJ2 44 45 14 17 ≤ 1726077002127 := by decide +kernel

theorem rows22250R_385 : rowsJ2 44 45 17 20 ≤ 2130212431783 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_379
#print axioms SieveCert.rows22250R_385
