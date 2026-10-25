/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4056–4070 of 5796

File 339 of 465: the parts `rows22250R_4056` … `rows22250R_4070` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98487 tests: row 131 columns 68–68, row 131 columns 69–69, row 131 columns
70–70, row 131 columns 71–71, row 131 columns 72–72, row 131 columns 73–73, row 131 columns 74–74, row 131 columns
75–75, row 131 columns 76–76, row 131 columns 77–77, row 131 columns 78–78, row 131 columns 79–80, row 131 columns
81–82, row 131 columns 83–86, row 131 columns 87–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4056 : rowsJ2 131 132 68 69 ≤ 4083574061276 := by decide +kernel

theorem rows22250R_4057 : rowsJ2 131 132 69 70 ≤ 4250352862360 := by decide +kernel

theorem rows22250R_4058 : rowsJ2 131 132 70 71 ≤ 4375594286628 := by decide +kernel

theorem rows22250R_4059 : rowsJ2 131 132 71 72 ≤ 4439938013526 := by decide +kernel

theorem rows22250R_4060 : rowsJ2 131 132 72 73 ≤ 4460996679310 := by decide +kernel

theorem rows22250R_4061 : rowsJ2 131 132 73 74 ≤ 4418974445676 := by decide +kernel

theorem rows22250R_4062 : rowsJ2 131 132 74 75 ≤ 4331435925447 := by decide +kernel

theorem rows22250R_4063 : rowsJ2 131 132 75 76 ≤ 3944534784775 := by decide +kernel

theorem rows22250R_4064 : rowsJ2 131 132 76 77 ≤ 3351530106109 := by decide +kernel

theorem rows22250R_4065 : rowsJ2 131 132 77 78 ≤ 2790940725290 := by decide +kernel

theorem rows22250R_4066 : rowsJ2 131 132 78 79 ≤ 2280959499264 := by decide +kernel

theorem rows22250R_4067 : rowsJ2 131 132 79 81 ≤ 3171517732807 := by decide +kernel

theorem rows22250R_4068 : rowsJ2 131 132 81 83 ≤ 1579803091961 := by decide +kernel

theorem rows22250R_4069 : rowsJ2 131 132 83 87 ≤ 283203109138 := by decide +kernel

theorem rows22250R_4070 : rowsJ2 131 132 87 90 ≤ 3166188668535 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4056
#print axioms SieveCert.rows22250R_4070
