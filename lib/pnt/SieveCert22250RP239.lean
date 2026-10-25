/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2608–2620 of 5796

File 239 of 465: the parts `rows22250R_2608` … `rows22250R_2620` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97093 tests: row 95 columns 45–45, row 95 columns 46–46, row 95 columns
47–47, row 95 columns 48–48, row 95 columns 49–49, row 95 columns 50–50, row 95 columns 51–51, row 95 columns 52–52,
row 95 columns 53–53, row 95 columns 54–54, row 95 columns 55–55, row 95 columns 56–56, row 95 columns 57–57), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2608 : rowsJ2 95 96 45 46 ≤ 12125240528635 := by decide +kernel

theorem rows22250R_2609 : rowsJ2 95 96 46 47 ≤ 13210119820040 := by decide +kernel

theorem rows22250R_2610 : rowsJ2 95 96 47 48 ≤ 14196238529916 := by decide +kernel

theorem rows22250R_2611 : rowsJ2 95 96 48 49 ≤ 13864364921838 := by decide +kernel

theorem rows22250R_2612 : rowsJ2 95 96 49 50 ≤ 9491103884779 := by decide +kernel

theorem rows22250R_2613 : rowsJ2 95 96 50 51 ≤ 5816214078742 := by decide +kernel

theorem rows22250R_2614 : rowsJ2 95 96 51 52 ≤ 2522809672701 := by decide +kernel

theorem rows22250R_2615 : rowsJ2 95 96 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2616 : rowsJ2 95 96 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2617 : rowsJ2 95 96 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2618 : rowsJ2 95 96 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2619 : rowsJ2 95 96 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2620 : rowsJ2 95 96 57 58 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2608
#print axioms SieveCert.rows22250R_2620
