/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3731–3745 of 5796

File 318 of 465: the parts `rows22250R_3731` … `rows22250R_3745` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 93813 tests: row 120 columns 88–90, row 120 columns 91–92, row 120 columns
93–94, row 120 columns 95–96, row 120 columns 97–98, row 120 columns 99–99, row 120 columns 100–100, row 120 columns
101–101, row 120 columns 102–102, row 120 columns 103–359, row 121 columns 0–27, row 121 columns 28–30, row 121
columns 31–32, row 121 columns 33–34, row 121 columns 35–36), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_3731 : rowsJ2 120 121 88 91 ≤ 2288693263156 := by decide +kernel

theorem rows22250R_3732 : rowsJ2 120 121 91 93 ≤ 3607155094423 := by decide +kernel

theorem rows22250R_3733 : rowsJ2 120 121 93 95 ≤ 5896073644088 := by decide +kernel

theorem rows22250R_3734 : rowsJ2 120 121 95 97 ≤ 8753868836220 := by decide +kernel

theorem rows22250R_3735 : rowsJ2 120 121 97 99 ≤ 12213711616779 := by decide +kernel

theorem rows22250R_3736 : rowsJ2 120 121 99 100 ≤ 7608191927340 := by decide +kernel

theorem rows22250R_3737 : rowsJ2 120 121 100 101 ≤ 8705477336704 := by decide +kernel

theorem rows22250R_3738 : rowsJ2 120 121 101 102 ≤ 9911745322124 := by decide +kernel

theorem rows22250R_3739 : rowsJ2 120 121 102 103 ≤ 11185605577127 := by decide +kernel

theorem rows22250R_3740 : rowsJ2 120 121 103 360 ≤ 1533354203330468 := by decide +kernel

theorem rows22250R_3741 : rowsJ2 121 122 0 28 ≤ 661485990367 := by decide +kernel

theorem rows22250R_3742 : rowsJ2 121 122 28 31 ≤ 5770690665062 := by decide +kernel

theorem rows22250R_3743 : rowsJ2 121 122 31 33 ≤ 9472722364782 := by decide +kernel

theorem rows22250R_3744 : rowsJ2 121 122 33 35 ≤ 15483979962798 := by decide +kernel

theorem rows22250R_3745 : rowsJ2 121 122 35 37 ≤ 17546259109713 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3731
#print axioms SieveCert.rows22250R_3745
