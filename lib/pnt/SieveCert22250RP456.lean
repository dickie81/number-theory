/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5647–5662 of 5796

File 456 of 465: the parts `rows22250R_5647` … `rows22250R_5662` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96605 tests: row 194 columns 44–44, row 194 columns 45–45, row 194 columns
46–359, row 195 columns 0–33, row 195 columns 34–35, row 195 columns 36–37, row 195 columns 38–38, row 195 columns
39–39, row 195 columns 40–40, row 195 columns 41–41, row 195 columns 42–42, row 195 columns 43–43, row 195 columns
44–44, row 195 columns 45–359, row 196 columns 0–33, row 196 columns 34–35), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5647 : rowsJ2 194 195 44 45 ≤ 24645870250282 := by decide +kernel

theorem rows22250R_5648 : rowsJ2 194 195 45 46 ≤ 22196335672728 := by decide +kernel

theorem rows22250R_5649 : rowsJ2 194 195 46 360 ≤ 3406290978926624 := by decide +kernel

theorem rows22250R_5650 : rowsJ2 195 196 0 34 ≤ 14360578201052 := by decide +kernel

theorem rows22250R_5651 : rowsJ2 195 196 34 36 ≤ 16689735969824 := by decide +kernel

theorem rows22250R_5652 : rowsJ2 195 196 36 38 ≤ 26276381373521 := by decide +kernel

theorem rows22250R_5653 : rowsJ2 195 196 38 39 ≤ 17456934815757 := by decide +kernel

theorem rows22250R_5654 : rowsJ2 195 196 39 40 ≤ 20712600164688 := by decide +kernel

theorem rows22250R_5655 : rowsJ2 195 196 40 41 ≤ 22668730260427 := by decide +kernel

theorem rows22250R_5656 : rowsJ2 195 196 41 42 ≤ 24689272889690 := by decide +kernel

theorem rows22250R_5657 : rowsJ2 195 196 42 43 ≤ 26772976682799 := by decide +kernel

theorem rows22250R_5658 : rowsJ2 195 196 43 44 ≤ 26484470871843 := by decide +kernel

theorem rows22250R_5659 : rowsJ2 195 196 44 45 ≤ 23899626716616 := by decide +kernel

theorem rows22250R_5660 : rowsJ2 195 196 45 360 ≤ 3525856493555982 := by decide +kernel

theorem rows22250R_5661 : rowsJ2 196 197 0 34 ≤ 16813255433363 := by decide +kernel

theorem rows22250R_5662 : rowsJ2 196 197 34 36 ≤ 18374113309903 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5647
#print axioms SieveCert.rows22250R_5662
