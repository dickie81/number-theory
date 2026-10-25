/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5632–5646 of 5796

File 455 of 465: the parts `rows22250R_5632` … `rows22250R_5646` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94516 tests: row 193 columns 41–41, row 193 columns 42–42, row 193 columns
43–43, row 193 columns 44–44, row 193 columns 45–45, row 193 columns 46–46, row 193 columns 47–359, row 194 columns
0–33, row 194 columns 34–36, row 194 columns 37–38, row 194 columns 39–39, row 194 columns 40–40, row 194 columns
41–41, row 194 columns 42–42, row 194 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_5632 : rowsJ2 193 194 41 42 ≤ 21699277359825 := by decide +kernel

theorem rows22250R_5633 : rowsJ2 193 194 42 43 ≤ 23635593364666 := by decide +kernel

theorem rows22250R_5634 : rowsJ2 193 194 43 44 ≤ 25632444668452 := by decide +kernel

theorem rows22250R_5635 : rowsJ2 193 194 44 45 ≤ 25359174006480 := by decide +kernel

theorem rows22250R_5636 : rowsJ2 193 194 45 46 ≤ 22887621633804 := by decide +kernel

theorem rows22250R_5637 : rowsJ2 193 194 46 47 ≤ 20566732369280 := by decide +kernel

theorem rows22250R_5638 : rowsJ2 193 194 47 360 ≤ 3285937739948146 := by decide +kernel

theorem rows22250R_5639 : rowsJ2 194 195 0 34 ≤ 12209217160690 := by decide +kernel

theorem rows22250R_5640 : rowsJ2 194 195 34 37 ≤ 25926265818024 := by decide +kernel

theorem rows22250R_5641 : rowsJ2 194 195 37 39 ≤ 29583891975989 := by decide +kernel

theorem rows22250R_5642 : rowsJ2 194 195 39 40 ≤ 19345489045615 := by decide +kernel

theorem rows22250R_5643 : rowsJ2 194 195 40 41 ≤ 21227919974293 := by decide +kernel

theorem rows22250R_5644 : rowsJ2 194 195 41 42 ≤ 23174161350544 := by decide +kernel

theorem rows22250R_5645 : rowsJ2 194 195 42 43 ≤ 25182824665360 := by decide +kernel

theorem rows22250R_5646 : rowsJ2 194 195 43 44 ≤ 27252793678027 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5632
#print axioms SieveCert.rows22250R_5646
