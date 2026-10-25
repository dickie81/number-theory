/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3790–3804 of 5796

File 322 of 465: the parts `rows22250R_3790` … `rows22250R_3804` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 92750 tests: row 122 columns 91–92, row 122 columns 93–94, row 122 columns
95–96, row 122 columns 97–98, row 122 columns 99–99, row 122 columns 100–100, row 122 columns 101–101, row 122
columns 102–359, row 123 columns 0–27, row 123 columns 28–30, row 123 columns 31–32, row 123 columns 33–34, row 123
columns 35–36, row 123 columns 37–38, row 123 columns 39–41), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3790 : rowsJ2 122 123 91 93 ≤ 4182753315381 := by decide +kernel

theorem rows22250R_3791 : rowsJ2 122 123 93 95 ≤ 6727966741814 := by decide +kernel

theorem rows22250R_3792 : rowsJ2 122 123 95 97 ≤ 9872036754027 := by decide +kernel

theorem rows22250R_3793 : rowsJ2 122 123 97 99 ≤ 13651798553128 := by decide +kernel

theorem rows22250R_3794 : rowsJ2 122 123 99 100 ≤ 8459008795722 := by decide +kernel

theorem rows22250R_3795 : rowsJ2 122 123 100 101 ≤ 9650547330505 := by decide +kernel

theorem rows22250R_3796 : rowsJ2 122 123 101 102 ≤ 10957180686143 := by decide +kernel

theorem rows22250R_3797 : rowsJ2 122 123 102 360 ≤ 1396868410334758 := by decide +kernel

theorem rows22250R_3798 : rowsJ2 123 124 0 28 ≤ 1241289546418 := by decide +kernel

theorem rows22250R_3799 : rowsJ2 123 124 28 31 ≤ 6964706963623 := by decide +kernel

theorem rows22250R_3800 : rowsJ2 123 124 31 33 ≤ 10918977004431 := by decide +kernel

theorem rows22250R_3801 : rowsJ2 123 124 33 35 ≤ 16318615434744 := by decide +kernel

theorem rows22250R_3802 : rowsJ2 123 124 35 37 ≤ 14385025689425 := by decide +kernel

theorem rows22250R_3803 : rowsJ2 123 124 37 39 ≤ 11229736539127 := by decide +kernel

theorem rows22250R_3804 : rowsJ2 123 124 39 42 ≤ 10419824496038 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3790
#print axioms SieveCert.rows22250R_3804
