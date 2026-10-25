/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4134–4147 of 4715

File 315 of 351: the parts `rows22250R_4134` … `rows22250R_4147` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98494 tests: row 157 columns 0–41, row 157 columns 42–44, row 157 columns
45–46, row 157 columns 47–47, row 157 columns 48–48, row 157 columns 49–49, row 157 columns 50–50, row 157 columns
51–51, row 157 columns 52–52, row 157 columns 53–53, row 157 columns 54–54, row 157 columns 55–55, row 157 columns
56–56, row 157 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4134 : rowsJ2 157 158 0 42 ≤ 10412763033939 := by decide +kernel

theorem rows22250R_4135 : rowsJ2 157 158 42 45 ≤ 14641564316976 := by decide +kernel

theorem rows22250R_4136 : rowsJ2 157 158 45 47 ≤ 14576088040400 := by decide +kernel

theorem rows22250R_4137 : rowsJ2 157 158 47 48 ≤ 8915965168955 := by decide +kernel

theorem rows22250R_4138 : rowsJ2 157 158 48 49 ≤ 10076748142367 := by decide +kernel

theorem rows22250R_4139 : rowsJ2 157 158 49 50 ≤ 11291387386645 := by decide +kernel

theorem rows22250R_4140 : rowsJ2 157 158 50 51 ≤ 12557914244694 := by decide +kernel

theorem rows22250R_4141 : rowsJ2 157 158 51 52 ≤ 13874553794958 := by decide +kernel

theorem rows22250R_4142 : rowsJ2 157 158 52 53 ≤ 15239715281910 := by decide +kernel

theorem rows22250R_4143 : rowsJ2 157 158 53 54 ≤ 16651983576442 := by decide +kernel

theorem rows22250R_4144 : rowsJ2 157 158 54 55 ≤ 16487164910657 := by decide +kernel

theorem rows22250R_4145 : rowsJ2 157 158 55 56 ≤ 14791629581012 := by decide +kernel

theorem rows22250R_4146 : rowsJ2 157 158 56 57 ≤ 13201241907550 := by decide +kernel

theorem rows22250R_4147 : rowsJ2 157 158 57 58 ≤ 11712931201168 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4134
#print axioms SieveCert.rows22250R_4147
