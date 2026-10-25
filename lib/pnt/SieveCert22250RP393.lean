/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4759–4772 of 5796

File 393 of 465: the parts `rows22250R_4759` … `rows22250R_4772` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93582 tests: row 153 columns 75–76, row 153 columns 77–79, row 153 columns
80–85, row 153 columns 86–359, row 154 columns 0–42, row 154 columns 43–49, row 154 columns 50–51, row 154 columns
52–53, row 154 columns 54–54, row 154 columns 55–55, row 154 columns 56–56, row 154 columns 57–57, row 154 columns
58–58, row 154 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4759 : rowsJ2 153 154 75 77 ≤ 5066814479956 := by decide +kernel

theorem rows22250R_4760 : rowsJ2 153 154 77 80 ≤ 4284409467596 := by decide +kernel

theorem rows22250R_4761 : rowsJ2 153 154 80 86 ≤ 1755538945547 := by decide +kernel

theorem rows22250R_4762 : rowsJ2 153 154 86 360 ≤ 1226836250207489 := by decide +kernel

theorem rows22250R_4763 : rowsJ2 154 155 0 43 ≤ 418383828090 := by decide +kernel

theorem rows22250R_4764 : rowsJ2 154 155 43 50 ≤ 6854058251122 := by decide +kernel

theorem rows22250R_4765 : rowsJ2 154 155 50 52 ≤ 5804263963174 := by decide +kernel

theorem rows22250R_4766 : rowsJ2 154 155 52 54 ≤ 8242819175028 := by decide +kernel

theorem rows22250R_4767 : rowsJ2 154 155 54 55 ≤ 5143986745535 := by decide +kernel

theorem rows22250R_4768 : rowsJ2 154 155 55 56 ≤ 5879829253535 := by decide +kernel

theorem rows22250R_4769 : rowsJ2 154 155 56 57 ≤ 6654280053106 := by decide +kernel

theorem rows22250R_4770 : rowsJ2 154 155 57 58 ≤ 7465895512804 := by decide +kernel

theorem rows22250R_4771 : rowsJ2 154 155 58 59 ≤ 8313345003639 := by decide +kernel

theorem rows22250R_4772 : rowsJ2 154 155 59 60 ≤ 9195405230951 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4759
#print axioms SieveCert.rows22250R_4772
