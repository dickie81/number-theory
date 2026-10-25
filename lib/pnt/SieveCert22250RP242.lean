/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2643–2653 of 5796

File 242 of 465: the parts `rows22250R_2643` … `rows22250R_2653` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 97491 tests: row 95 columns 94–94, row 95 columns 95–359, row 96 columns
0–16, row 96 columns 17–19, row 96 columns 20–23, row 96 columns 24–29, row 96 columns 30–35, row 96 columns 36–38,
row 96 columns 39–40, row 96 columns 41–41, row 96 columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_2643 : rowsJ2 95 96 94 95 ≤ 5862274263996 := by decide +kernel

theorem rows22250R_2644 : rowsJ2 95 96 95 360 ≤ 5278828029433 := by decide +kernel

theorem rows22250R_2645 : rowsJ2 96 97 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2646 : rowsJ2 96 97 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2647 : rowsJ2 96 97 20 24 ≤ 0 := by decide +kernel

theorem rows22250R_2648 : rowsJ2 96 97 24 30 ≤ 0 := by decide +kernel

theorem rows22250R_2649 : rowsJ2 96 97 30 36 ≤ 2106353872519 := by decide +kernel

theorem rows22250R_2650 : rowsJ2 96 97 36 39 ≤ 9789289451266 := by decide +kernel

theorem rows22250R_2651 : rowsJ2 96 97 39 41 ≤ 12567480545822 := by decide +kernel

theorem rows22250R_2652 : rowsJ2 96 97 41 42 ≤ 7963005316217 := by decide +kernel

theorem rows22250R_2653 : rowsJ2 96 97 42 43 ≤ 9102537514282 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2643
#print axioms SieveCert.rows22250R_2653
