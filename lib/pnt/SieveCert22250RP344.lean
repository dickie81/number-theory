/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4130–4144 of 5796

File 344 of 465: the parts `rows22250R_4130` … `rows22250R_4144` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94433 tests: row 133 columns 78–78, row 133 columns 79–79, row 133 columns
80–81, row 133 columns 82–83, row 133 columns 84–86, row 133 columns 87–89, row 133 columns 90–92, row 133 columns
93–94, row 133 columns 95–96, row 133 columns 97–359, row 134 columns 0–25, row 134 columns 26–28, row 134 columns
29–32, row 134 columns 33–39, row 134 columns 40–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4130 : rowsJ2 133 134 78 79 ≤ 2762073276481 := by decide +kernel

theorem rows22250R_4131 : rowsJ2 133 134 79 80 ≤ 2281025254827 := by decide +kernel

theorem rows22250R_4132 : rowsJ2 133 134 80 82 ≤ 3293618746139 := by decide +kernel

theorem rows22250R_4133 : rowsJ2 133 134 82 84 ≤ 1846391019532 := by decide +kernel

theorem rows22250R_4134 : rowsJ2 133 134 84 87 ≤ 688628047021 := by decide +kernel

theorem rows22250R_4135 : rowsJ2 133 134 87 90 ≤ 3580105948148 := by decide +kernel

theorem rows22250R_4136 : rowsJ2 133 134 90 93 ≤ 10823240964370 := by decide +kernel

theorem rows22250R_4137 : rowsJ2 133 134 93 95 ≤ 12479020943123 := by decide +kernel

theorem rows22250R_4138 : rowsJ2 133 134 95 97 ≤ 17649693586523 := by decide +kernel

theorem rows22250R_4139 : rowsJ2 133 134 97 360 ≤ 809333306080411 := by decide +kernel

theorem rows22250R_4140 : rowsJ2 134 135 0 26 ≤ 2253142558500 := by decide +kernel

theorem rows22250R_4141 : rowsJ2 134 135 26 29 ≤ 10643156182110 := by decide +kernel

theorem rows22250R_4142 : rowsJ2 134 135 29 33 ≤ 12171518594403 := by decide +kernel

theorem rows22250R_4143 : rowsJ2 134 135 33 40 ≤ 5154645865144 := by decide +kernel

theorem rows22250R_4144 : rowsJ2 134 135 40 57 ≤ 1421999106066 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4130
#print axioms SieveCert.rows22250R_4144
