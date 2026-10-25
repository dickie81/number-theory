/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 569–579 of 4715

File 56 of 351: the parts `rows22250R_569` … `rows22250R_579` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 96178 tests: row 51 columns 36–36, row 51 columns 37–37, row 51 columns
38–38, row 51 columns 39–39, row 51 columns 40–40, row 51 columns 41–41, row 51 columns 42–42, row 51 columns 43–43,
row 51 columns 44–44, row 51 columns 45–45, row 51 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_569 : rowsJ2 51 52 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_570 : rowsJ2 51 52 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_571 : rowsJ2 51 52 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_572 : rowsJ2 51 52 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_573 : rowsJ2 51 52 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_574 : rowsJ2 51 52 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_575 : rowsJ2 51 52 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_576 : rowsJ2 51 52 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_577 : rowsJ2 51 52 44 45 ≤ 75266102921 := by decide +kernel

theorem rows22250R_578 : rowsJ2 51 52 45 46 ≤ 295419630621 := by decide +kernel

theorem rows22250R_579 : rowsJ2 51 52 46 47 ≤ 881339764121 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_569
#print axioms SieveCert.rows22250R_579
