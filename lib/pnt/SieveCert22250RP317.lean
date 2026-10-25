/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3717–3730 of 5796

File 317 of 465: the parts `rows22250R_3717` … `rows22250R_3730` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 99236 tests: row 120 columns 36–37, row 120 columns 38–39, row 120 columns
40–41, row 120 columns 42–44, row 120 columns 45–49, row 120 columns 50–61, row 120 columns 62–65, row 120 columns
66–68, row 120 columns 69–71, row 120 columns 72–75, row 120 columns 76–78, row 120 columns 79–81, row 120 columns
82–84, row 120 columns 85–87), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3717 : rowsJ2 120 121 36 38 ≤ 17445014142197 := by decide +kernel

theorem rows22250R_3718 : rowsJ2 120 121 38 40 ≤ 14141634486357 := by decide +kernel

theorem rows22250R_3719 : rowsJ2 120 121 40 42 ≤ 9684911304968 := by decide +kernel

theorem rows22250R_3720 : rowsJ2 120 121 42 45 ≤ 7856582342587 := by decide +kernel

theorem rows22250R_3721 : rowsJ2 120 121 45 50 ≤ 2530848914414 := by decide +kernel

theorem rows22250R_3722 : rowsJ2 120 121 50 62 ≤ 308074403620 := by decide +kernel

theorem rows22250R_3723 : rowsJ2 120 121 62 66 ≤ 2431207327638 := by decide +kernel

theorem rows22250R_3724 : rowsJ2 120 121 66 69 ≤ 2804463047756 := by decide +kernel

theorem rows22250R_3725 : rowsJ2 120 121 69 72 ≤ 2112311714329 := by decide +kernel

theorem rows22250R_3726 : rowsJ2 120 121 72 76 ≤ 301937549414 := by decide +kernel

theorem rows22250R_3727 : rowsJ2 120 121 76 79 ≤ 0 := by decide +kernel

theorem rows22250R_3728 : rowsJ2 120 121 79 82 ≤ 68101043858 := by decide +kernel

theorem rows22250R_3729 : rowsJ2 120 121 82 85 ≤ 11485374670 := by decide +kernel

theorem rows22250R_3730 : rowsJ2 120 121 85 88 ≤ 194185560605 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3717
#print axioms SieveCert.rows22250R_3730
