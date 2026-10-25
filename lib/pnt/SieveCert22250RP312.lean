/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3639–3655 of 5796

File 312 of 465: the parts `rows22250R_3639` … `rows22250R_3655` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 95825 tests: row 117 columns 93–94, row 117 columns 95–96, row 117 columns
97–98, row 117 columns 99–99, row 117 columns 100–100, row 117 columns 101–101, row 117 columns 102–102, row 117
columns 103–103, row 117 columns 104–104, row 117 columns 105–359, row 118 columns 0–26, row 118 columns 27–30, row
118 columns 31–32, row 118 columns 33–34, row 118 columns 35–35, row 118 columns 36–36, row 118 columns 37–37), each
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

theorem rows22250R_3639 : rowsJ2 117 118 93 95 ≤ 4727757372521 := by decide +kernel

theorem rows22250R_3640 : rowsJ2 117 118 95 97 ≤ 7192240660955 := by decide +kernel

theorem rows22250R_3641 : rowsJ2 117 118 97 99 ≤ 10213840144415 := by decide +kernel

theorem rows22250R_3642 : rowsJ2 117 118 99 100 ≤ 6417625947770 := by decide +kernel

theorem rows22250R_3643 : rowsJ2 117 118 100 101 ≤ 7407530408928 := by decide +kernel

theorem rows22250R_3644 : rowsJ2 117 118 101 102 ≤ 8455752440390 := by decide +kernel

theorem rows22250R_3645 : rowsJ2 117 118 102 103 ≤ 9607732748636 := by decide +kernel

theorem rows22250R_3646 : rowsJ2 117 118 103 104 ≤ 10822996173293 := by decide +kernel

theorem rows22250R_3647 : rowsJ2 117 118 104 105 ≤ 12148434661644 := by decide +kernel

theorem rows22250R_3648 : rowsJ2 117 118 105 360 ≤ 1144770933889875 := by decide +kernel

theorem rows22250R_3649 : rowsJ2 118 119 0 27 ≤ 0 := by decide +kernel

theorem rows22250R_3650 : rowsJ2 118 119 27 31 ≤ 4119387150411 := by decide +kernel

theorem rows22250R_3651 : rowsJ2 118 119 31 33 ≤ 7314912761582 := by decide +kernel

theorem rows22250R_3652 : rowsJ2 118 119 33 35 ≤ 13137450551771 := by decide +kernel

theorem rows22250R_3653 : rowsJ2 118 119 35 36 ≤ 8898185741889 := by decide +kernel

theorem rows22250R_3654 : rowsJ2 118 119 36 37 ≤ 10881724972756 := by decide +kernel

theorem rows22250R_3655 : rowsJ2 118 119 37 38 ≤ 9922715276248 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3639
#print axioms SieveCert.rows22250R_3655
