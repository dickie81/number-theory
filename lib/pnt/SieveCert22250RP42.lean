/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 430–438 of 4715

File 42 of 351: the parts `rows22250R_430` … `rows22250R_438` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 99398 tests: row 46 columns 38–38, row 46 columns 39–39, row 46 columns
40–40, row 46 columns 41–41, row 46 columns 42–42, row 46 columns 43–43, row 46 columns 44–44, row 46 columns 45–45,
row 46 columns 46–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_430 : rowsJ2 46 47 38 39 ≤ 28521910103 := by decide +kernel

theorem rows22250R_431 : rowsJ2 46 47 39 40 ≤ 18552751174 := by decide +kernel

theorem rows22250R_432 : rowsJ2 46 47 40 41 ≤ 12791865249 := by decide +kernel

theorem rows22250R_433 : rowsJ2 46 47 41 42 ≤ 9959051597 := by decide +kernel

theorem rows22250R_434 : rowsJ2 46 47 42 43 ≤ 8585332671 := by decide +kernel

theorem rows22250R_435 : rowsJ2 46 47 43 44 ≤ 5725518550 := by decide +kernel

theorem rows22250R_436 : rowsJ2 46 47 44 45 ≤ 83642458085 := by decide +kernel

theorem rows22250R_437 : rowsJ2 46 47 45 46 ≤ 313465560130 := by decide +kernel

theorem rows22250R_438 : rowsJ2 46 47 46 340 ≤ 930182133424 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_430
#print axioms SieveCert.rows22250R_438
