/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 355–360 of 4715

File 33 of 351: the parts `rows22250R_355` … `rows22250R_360` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, work 89864 in units of a depth-4 test: row 43 columns 36–36, row 43 columns
37–37, row 43 columns 38–38, row 43 columns 39–39, row 43 columns 40–40, row 43 columns 41–41), each a sum of
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

theorem rows22250R_355 : rowsJ2 43 44 36 37 ≤ 151960171525 := by decide +kernel

theorem rows22250R_356 : rowsJ2 43 44 37 38 ≤ 122783538995 := by decide +kernel

theorem rows22250R_357 : rowsJ2 43 44 38 39 ≤ 97980895825 := by decide +kernel

theorem rows22250R_358 : rowsJ2 43 44 39 40 ≤ 75082526848 := by decide +kernel

theorem rows22250R_359 : rowsJ2 43 44 40 41 ≤ 56559237426 := by decide +kernel

theorem rows22250R_360 : rowsJ2 43 44 41 42 ≤ 40737726001 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_355
#print axioms SieveCert.rows22250R_360
