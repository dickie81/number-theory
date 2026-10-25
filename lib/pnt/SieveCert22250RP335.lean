/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3995–4009 of 5796

File 335 of 465: the parts `rows22250R_3995` … `rows22250R_4009` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95398 tests: row 129 columns 70–70, row 129 columns 71–71, row 129 columns
72–72, row 129 columns 73–73, row 129 columns 74–74, row 129 columns 75–75, row 129 columns 76–76, row 129 columns
77–77, row 129 columns 78–79, row 129 columns 80–82, row 129 columns 83–86, row 129 columns 87–89, row 129 columns
90–92, row 129 columns 93–94, row 129 columns 95–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_3995 : rowsJ2 129 130 70 71 ≤ 3581225628176 := by decide +kernel

theorem rows22250R_3996 : rowsJ2 129 130 71 72 ≤ 3598043903217 := by decide +kernel

theorem rows22250R_3997 : rowsJ2 129 130 72 73 ≤ 3571053537783 := by decide +kernel

theorem rows22250R_3998 : rowsJ2 129 130 73 74 ≤ 3480206527416 := by decide +kernel

theorem rows22250R_3999 : rowsJ2 129 130 74 75 ≤ 3343232833375 := by decide +kernel

theorem rows22250R_4000 : rowsJ2 129 130 75 76 ≤ 3139597672380 := by decide +kernel

theorem rows22250R_4001 : rowsJ2 129 130 76 77 ≤ 2730409999181 := by decide +kernel

theorem rows22250R_4002 : rowsJ2 129 130 77 78 ≤ 2171428147740 := by decide +kernel

theorem rows22250R_4003 : rowsJ2 129 130 78 80 ≤ 2847938519814 := by decide +kernel

theorem rows22250R_4004 : rowsJ2 129 130 80 83 ≤ 1109516197650 := by decide +kernel

theorem rows22250R_4005 : rowsJ2 129 130 83 87 ≤ 0 := by decide +kernel

theorem rows22250R_4006 : rowsJ2 129 130 87 90 ≤ 2780794209224 := by decide +kernel

theorem rows22250R_4007 : rowsJ2 129 130 90 93 ≤ 8634404715339 := by decide +kernel

theorem rows22250R_4008 : rowsJ2 129 130 93 95 ≤ 10111017801481 := by decide +kernel

theorem rows22250R_4009 : rowsJ2 129 130 95 97 ≤ 14441793366505 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3995
#print axioms SieveCert.rows22250R_4009
