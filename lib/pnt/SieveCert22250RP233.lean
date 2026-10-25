/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2540–2546 of 5796

File 233 of 465: the parts `rows22250R_2540` … `rows22250R_2546` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 85226 tests: row 93 columns 86–86, row 93 columns 87–87, row 93 columns
88–88, row 93 columns 89–89, row 93 columns 90–90, row 93 columns 91–91, row 93 columns 92–92), each a sum of
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

theorem rows22250R_2540 : rowsJ2 93 94 86 87 ≤ 1600706121974 := by decide +kernel

theorem rows22250R_2541 : rowsJ2 93 94 87 88 ≤ 2112236398231 := by decide +kernel

theorem rows22250R_2542 : rowsJ2 93 94 88 89 ≤ 2749662132196 := by decide +kernel

theorem rows22250R_2543 : rowsJ2 93 94 89 90 ≤ 3507130108812 := by decide +kernel

theorem rows22250R_2544 : rowsJ2 93 94 90 91 ≤ 4404677876302 := by decide +kernel

theorem rows22250R_2545 : rowsJ2 93 94 91 92 ≤ 5438591057065 := by decide +kernel

theorem rows22250R_2546 : rowsJ2 93 94 92 93 ≤ 6633958187910 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2540
#print axioms SieveCert.rows22250R_2546
