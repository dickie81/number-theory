/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2690–2700 of 5796

File 246 of 465: the parts `rows22250R_2690` … `rows22250R_2700` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98081 tests: row 96 columns 94–94, row 96 columns 95–95, row 96 columns
96–359, row 97 columns 0–15, row 97 columns 16–19, row 97 columns 20–24, row 97 columns 25–31, row 97 columns 32–35,
row 97 columns 36–37, row 97 columns 38–39, row 97 columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`)
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

theorem rows22250R_2690 : rowsJ2 96 97 94 95 ≤ 4980229711816 := by decide +kernel

theorem rows22250R_2691 : rowsJ2 96 97 95 96 ≤ 4496457563378 := by decide +kernel

theorem rows22250R_2692 : rowsJ2 96 97 96 360 ≤ 4379061674778 := by decide +kernel

theorem rows22250R_2693 : rowsJ2 97 98 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2694 : rowsJ2 97 98 16 20 ≤ 0 := by decide +kernel

theorem rows22250R_2695 : rowsJ2 97 98 20 25 ≤ 0 := by decide +kernel

theorem rows22250R_2696 : rowsJ2 97 98 25 32 ≤ 0 := by decide +kernel

theorem rows22250R_2697 : rowsJ2 97 98 32 36 ≤ 2583663638551 := by decide +kernel

theorem rows22250R_2698 : rowsJ2 97 98 36 38 ≤ 6017826983750 := by decide +kernel

theorem rows22250R_2699 : rowsJ2 97 98 38 40 ≤ 10886252164099 := by decide +kernel

theorem rows22250R_2700 : rowsJ2 97 98 40 41 ≤ 7285659099400 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2690
#print axioms SieveCert.rows22250R_2700
