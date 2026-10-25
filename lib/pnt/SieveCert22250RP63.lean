/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 588–594 of 5796

File 63 of 465: the parts `rows22250R_588` … `rows22250R_594` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 99315 tests: row 51 columns 37–37, row 51 columns 38–38, row 51 columns
39–39, row 51 columns 40–40, row 51 columns 41–41, row 51 columns 42–42, row 51 columns 43–43), each a sum of
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

theorem rows22250R_588 : rowsJ2 51 52 37 38 ≤ 20259813301 := by decide +kernel

theorem rows22250R_589 : rowsJ2 51 52 38 39 ≤ 11766548706 := by decide +kernel

theorem rows22250R_590 : rowsJ2 51 52 39 40 ≤ 6781353410 := by decide +kernel

theorem rows22250R_591 : rowsJ2 51 52 40 41 ≤ 1822816388 := by decide +kernel

theorem rows22250R_592 : rowsJ2 51 52 41 42 ≤ 907436372 := by decide +kernel

theorem rows22250R_593 : rowsJ2 51 52 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_594 : rowsJ2 51 52 43 44 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_588
#print axioms SieveCert.rows22250R_594
