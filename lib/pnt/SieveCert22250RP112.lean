/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1069–1083 of 5796

File 112 of 465: the parts `rows22250R_1069` … `rows22250R_1083` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98535 tests: row 64 columns 37–37, row 64 columns 38–38, row 64 columns
39–39, row 64 columns 40–40, row 64 columns 41–41, row 64 columns 42–42, row 64 columns 43–43, row 64 columns 44–44,
row 64 columns 45–45, row 64 columns 46–46, row 64 columns 47–47, row 64 columns 48–48, row 64 columns 49–49, row 64
columns 50–50, row 64 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1069 : rowsJ2 64 65 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1070 : rowsJ2 64 65 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1071 : rowsJ2 64 65 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1072 : rowsJ2 64 65 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1073 : rowsJ2 64 65 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1074 : rowsJ2 64 65 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1075 : rowsJ2 64 65 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1076 : rowsJ2 64 65 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1077 : rowsJ2 64 65 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1078 : rowsJ2 64 65 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1079 : rowsJ2 64 65 47 48 ≤ 108521961337 := by decide +kernel

theorem rows22250R_1080 : rowsJ2 64 65 48 49 ≤ 486377953169 := by decide +kernel

theorem rows22250R_1081 : rowsJ2 64 65 49 50 ≤ 905699287600 := by decide +kernel

theorem rows22250R_1082 : rowsJ2 64 65 50 51 ≤ 1362198501948 := by decide +kernel

theorem rows22250R_1083 : rowsJ2 64 65 51 52 ≤ 1960880258668 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1069
#print axioms SieveCert.rows22250R_1083
