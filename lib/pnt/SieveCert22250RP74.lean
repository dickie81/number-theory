/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 685–693 of 5796

File 74 of 465: the parts `rows22250R_685` … `rows22250R_693` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 98840 tests: row 54 columns 38–38, row 54 columns 39–39, row 54 columns
40–40, row 54 columns 41–41, row 54 columns 42–42, row 54 columns 43–43, row 54 columns 44–44, row 54 columns 45–45,
row 54 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_685 : rowsJ2 54 55 38 39 ≤ 911319668 := by decide +kernel

theorem rows22250R_686 : rowsJ2 54 55 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_687 : rowsJ2 54 55 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_688 : rowsJ2 54 55 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_689 : rowsJ2 54 55 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_690 : rowsJ2 54 55 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_691 : rowsJ2 54 55 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_692 : rowsJ2 54 55 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_693 : rowsJ2 54 55 46 47 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_685
#print axioms SieveCert.rows22250R_693
