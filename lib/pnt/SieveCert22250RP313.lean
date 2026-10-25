/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4105–4120 of 4715

File 313 of 351: the parts `rows22250R_4105` … `rows22250R_4120` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97854 tests: row 155 columns 58–58, row 155 columns 59–59, row 155 columns
60–60, row 155 columns 61–61, row 155 columns 62–62, row 155 columns 63–64, row 155 columns 65–67, row 155 columns
68–339, row 156 columns 0–41, row 156 columns 42–44, row 156 columns 45–46, row 156 columns 47–47, row 156 columns
48–48, row 156 columns 49–49, row 156 columns 50–50, row 156 columns 51–51), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4105 : rowsJ2 155 156 58 59 ≤ 11302742522020 := by decide +kernel

theorem rows22250R_4106 : rowsJ2 155 156 59 60 ≤ 9963084731678 := by decide +kernel

theorem rows22250R_4107 : rowsJ2 155 156 60 61 ≤ 8716383032895 := by decide +kernel

theorem rows22250R_4108 : rowsJ2 155 156 61 62 ≤ 7560336855245 := by decide +kernel

theorem rows22250R_4109 : rowsJ2 155 156 62 63 ≤ 6492827154476 := by decide +kernel

theorem rows22250R_4110 : rowsJ2 155 156 63 65 ≤ 10127712587305 := by decide +kernel

theorem rows22250R_4111 : rowsJ2 155 156 65 68 ≤ 9295587528777 := by decide +kernel

theorem rows22250R_4112 : rowsJ2 155 156 68 340 ≤ 2593357811187165 := by decide +kernel

theorem rows22250R_4113 : rowsJ2 156 157 0 42 ≤ 8547058812798 := by decide +kernel

theorem rows22250R_4114 : rowsJ2 156 157 42 45 ≤ 13049213239583 := by decide +kernel

theorem rows22250R_4115 : rowsJ2 156 157 45 47 ≤ 13270608311823 := by decide +kernel

theorem rows22250R_4116 : rowsJ2 156 157 47 48 ≤ 8191172270112 := by decide +kernel

theorem rows22250R_4117 : rowsJ2 156 157 48 49 ≤ 9304261421006 := by decide +kernel

theorem rows22250R_4118 : rowsJ2 156 157 49 50 ≤ 10471380253138 := by decide +kernel

theorem rows22250R_4119 : rowsJ2 156 157 50 51 ≤ 11690494133097 := by decide +kernel

theorem rows22250R_4120 : rowsJ2 156 157 51 52 ≤ 12959762042988 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4105
#print axioms SieveCert.rows22250R_4120
