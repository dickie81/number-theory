/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3608–3624 of 5796

File 310 of 465: the parts `rows22250R_3608` … `rows22250R_3624` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98004 tests: row 116 columns 96–97, row 116 columns 98–98, row 116 columns
99–99, row 116 columns 100–100, row 116 columns 101–101, row 116 columns 102–102, row 116 columns 103–103, row 116
columns 104–104, row 116 columns 105–359, row 117 columns 0–26, row 117 columns 27–31, row 117 columns 32–33, row
117 columns 34–35, row 117 columns 36–36, row 117 columns 37–37, row 117 columns 38–38, row 117 columns 39–40), each
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

theorem rows22250R_3608 : rowsJ2 116 117 96 98 ≤ 8099395930592 := by decide +kernel

theorem rows22250R_3609 : rowsJ2 116 117 98 99 ≤ 5196507935452 := by decide +kernel

theorem rows22250R_3610 : rowsJ2 116 117 99 100 ≤ 6071176017568 := by decide +kernel

theorem rows22250R_3611 : rowsJ2 116 117 100 101 ≤ 7000117234180 := by decide +kernel

theorem rows22250R_3612 : rowsJ2 116 117 101 102 ≤ 8027426223338 := by decide +kernel

theorem rows22250R_3613 : rowsJ2 116 117 102 103 ≤ 9113387704365 := by decide +kernel

theorem rows22250R_3614 : rowsJ2 116 117 103 104 ≤ 10303453841765 := by decide +kernel

theorem rows22250R_3615 : rowsJ2 116 117 104 105 ≤ 11557213531866 := by decide +kernel

theorem rows22250R_3616 : rowsJ2 116 117 105 360 ≤ 1071182073543657 := by decide +kernel

theorem rows22250R_3617 : rowsJ2 117 118 0 27 ≤ 0 := by decide +kernel

theorem rows22250R_3618 : rowsJ2 117 118 27 32 ≤ 6159553537575 := by decide +kernel

theorem rows22250R_3619 : rowsJ2 117 118 32 34 ≤ 9308388029440 := by decide +kernel

theorem rows22250R_3620 : rowsJ2 117 118 34 36 ≤ 15446280448440 := by decide +kernel

theorem rows22250R_3621 : rowsJ2 117 118 36 37 ≤ 10276552609980 := by decide +kernel

theorem rows22250R_3622 : rowsJ2 117 118 37 38 ≤ 10820844705162 := by decide +kernel

theorem rows22250R_3623 : rowsJ2 117 118 38 39 ≤ 9868510264479 := by decide +kernel

theorem rows22250R_3624 : rowsJ2 117 118 39 41 ≤ 16496600489749 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3608
#print axioms SieveCert.rows22250R_3624
