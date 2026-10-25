/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 593–601 of 4715

File 58 of 351: the parts `rows22250R_593` … `rows22250R_601` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 98135 tests: row 52 columns 29–29, row 52 columns 30–30, row 52 columns
31–31, row 52 columns 32–32, row 52 columns 33–33, row 52 columns 34–34, row 52 columns 35–35, row 52 columns 36–36,
row 52 columns 37–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_593 : rowsJ2 52 53 29 30 ≤ 46674731684 := by decide +kernel

theorem rows22250R_594 : rowsJ2 52 53 30 31 ≤ 31579667693 := by decide +kernel

theorem rows22250R_595 : rowsJ2 52 53 31 32 ≤ 20212318255 := by decide +kernel

theorem rows22250R_596 : rowsJ2 52 53 32 33 ≤ 10124402740 := by decide +kernel

theorem rows22250R_597 : rowsJ2 52 53 33 34 ≤ 4444801834 := by decide +kernel

theorem rows22250R_598 : rowsJ2 52 53 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_599 : rowsJ2 52 53 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_600 : rowsJ2 52 53 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_601 : rowsJ2 52 53 37 38 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_593
#print axioms SieveCert.rows22250R_601
