/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2738–2747 of 5796

File 250 of 465: the parts `rows22250R_2738` … `rows22250R_2747` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97862 tests: row 97 columns 94–94, row 97 columns 95–95, row 97 columns
96–96, row 97 columns 97–359, row 98 columns 0–15, row 98 columns 16–19, row 98 columns 20–24, row 98 columns 25–32,
row 98 columns 33–36, row 98 columns 37–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2738 : rowsJ2 97 98 94 95 ≤ 4189251629726 := by decide +kernel

theorem rows22250R_2739 : rowsJ2 97 98 95 96 ≤ 4043492793356 := by decide +kernel

theorem rows22250R_2740 : rowsJ2 97 98 96 97 ≤ 3966935070018 := by decide +kernel

theorem rows22250R_2741 : rowsJ2 97 98 97 360 ≤ 3947709141665 := by decide +kernel

theorem rows22250R_2742 : rowsJ2 98 99 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2743 : rowsJ2 98 99 16 20 ≤ 0 := by decide +kernel

theorem rows22250R_2744 : rowsJ2 98 99 20 25 ≤ 0 := by decide +kernel

theorem rows22250R_2745 : rowsJ2 98 99 25 33 ≤ 81079934739 := by decide +kernel

theorem rows22250R_2746 : rowsJ2 98 99 33 37 ≤ 5916240490385 := by decide +kernel

theorem rows22250R_2747 : rowsJ2 98 99 37 39 ≤ 8867012392014 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2738
#print axioms SieveCert.rows22250R_2747
