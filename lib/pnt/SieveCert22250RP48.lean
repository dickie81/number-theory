/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 473–477 of 5796

File 48 of 465: the parts `rows22250R_473` … `rows22250R_477` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 89863 tests: row 47 columns 36–36, row 47 columns 37–37, row 47 columns
38–38, row 47 columns 39–39, row 47 columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_473 : rowsJ2 47 48 36 37 ≤ 119654934559 := by decide +kernel

theorem rows22250R_474 : rowsJ2 47 48 37 38 ≤ 99207578529 := by decide +kernel

theorem rows22250R_475 : rowsJ2 47 48 38 39 ≤ 78427842101 := by decide +kernel

theorem rows22250R_476 : rowsJ2 47 48 39 40 ≤ 63316518146 := by decide +kernel

theorem rows22250R_477 : rowsJ2 47 48 40 41 ≤ 48310141105 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_473
#print axioms SieveCert.rows22250R_477
