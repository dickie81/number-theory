/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 538–547 of 4715

File 53 of 351: the parts `rows22250R_538` … `rows22250R_547` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 98335 tests: row 50 columns 35–35, row 50 columns 36–36, row 50 columns
37–37, row 50 columns 38–38, row 50 columns 39–39, row 50 columns 40–40, row 50 columns 41–41, row 50 columns 42–42,
row 50 columns 43–43, row 50 columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_538 : rowsJ2 50 51 35 36 ≤ 7147656510 := by decide +kernel

theorem rows22250R_539 : rowsJ2 50 51 36 37 ≤ 2726661021 := by decide +kernel

theorem rows22250R_540 : rowsJ2 50 51 37 38 ≤ 2049598335 := by decide +kernel

theorem rows22250R_541 : rowsJ2 50 51 38 39 ≤ 2054420645 := by decide +kernel

theorem rows22250R_542 : rowsJ2 50 51 39 40 ≤ 1373403755 := by decide +kernel

theorem rows22250R_543 : rowsJ2 50 51 40 41 ≤ 1377434382 := by decide +kernel

theorem rows22250R_544 : rowsJ2 50 51 41 42 ≤ 690976774 := by decide +kernel

theorem rows22250R_545 : rowsJ2 50 51 42 43 ≤ 693408154 := by decide +kernel

theorem rows22250R_546 : rowsJ2 50 51 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_547 : rowsJ2 50 51 44 45 ≤ 76041785060 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_538
#print axioms SieveCert.rows22250R_547
