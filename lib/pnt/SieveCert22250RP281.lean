/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3143–3158 of 5796

File 281 of 465: the parts `rows22250R_3143` … `rows22250R_3158` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99430 tests: row 106 columns 41–41, row 106 columns 42–42, row 106 columns
43–43, row 106 columns 44–44, row 106 columns 45–45, row 106 columns 46–46, row 106 columns 47–47, row 106 columns
48–48, row 106 columns 49–49, row 106 columns 50–51, row 106 columns 52–53, row 106 columns 54–55, row 106 columns
56–58, row 106 columns 59–63, row 106 columns 64–70, row 106 columns 71–75), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3143 : rowsJ2 106 107 41 42 ≤ 13004606315888 := by decide +kernel

theorem rows22250R_3144 : rowsJ2 106 107 42 43 ≤ 14234226944909 := by decide +kernel

theorem rows22250R_3145 : rowsJ2 106 107 43 44 ≤ 12674760127024 := by decide +kernel

theorem rows22250R_3146 : rowsJ2 106 107 44 45 ≤ 11182806424678 := by decide +kernel

theorem rows22250R_3147 : rowsJ2 106 107 45 46 ≤ 9707378704439 := by decide +kernel

theorem rows22250R_3148 : rowsJ2 106 107 46 47 ≤ 8297825756427 := by decide +kernel

theorem rows22250R_3149 : rowsJ2 106 107 47 48 ≤ 6954034720318 := by decide +kernel

theorem rows22250R_3150 : rowsJ2 106 107 48 49 ≤ 5759267928140 := by decide +kernel

theorem rows22250R_3151 : rowsJ2 106 107 49 50 ≤ 4710687235948 := by decide +kernel

theorem rows22250R_3152 : rowsJ2 106 107 50 52 ≤ 6848055074431 := by decide +kernel

theorem rows22250R_3153 : rowsJ2 106 107 52 54 ≤ 4052867758826 := by decide +kernel

theorem rows22250R_3154 : rowsJ2 106 107 54 56 ≤ 1783206168650 := by decide +kernel

theorem rows22250R_3155 : rowsJ2 106 107 56 59 ≤ 355909192625 := by decide +kernel

theorem rows22250R_3156 : rowsJ2 106 107 59 64 ≤ 0 := by decide +kernel

theorem rows22250R_3157 : rowsJ2 106 107 64 71 ≤ 0 := by decide +kernel

theorem rows22250R_3158 : rowsJ2 106 107 71 76 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3143
#print axioms SieveCert.rows22250R_3158
