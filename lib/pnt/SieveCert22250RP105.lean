/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1157–1166 of 4715

File 105 of 351: the parts `rows22250R_1157` … `rows22250R_1166` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 87697 tests: row 66 columns 45–45, row 66 columns 46–46, row 66 columns
47–47, row 66 columns 48–48, row 66 columns 49–49, row 66 columns 50–50, row 66 columns 51–51, row 66 columns 52–52,
row 66 columns 53–53, row 66 columns 54–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1157 : rowsJ2 66 67 45 46 ≤ 256215788181 := by decide +kernel

theorem rows22250R_1158 : rowsJ2 66 67 46 47 ≤ 764381032647 := by decide +kernel

theorem rows22250R_1159 : rowsJ2 66 67 47 48 ≤ 1517942162928 := by decide +kernel

theorem rows22250R_1160 : rowsJ2 66 67 48 49 ≤ 2242986807910 := by decide +kernel

theorem rows22250R_1161 : rowsJ2 66 67 49 50 ≤ 3067949808309 := by decide +kernel

theorem rows22250R_1162 : rowsJ2 66 67 50 51 ≤ 4121387729704 := by decide +kernel

theorem rows22250R_1163 : rowsJ2 66 67 51 52 ≤ 5301866048553 := by decide +kernel

theorem rows22250R_1164 : rowsJ2 66 67 52 53 ≤ 6187738264836 := by decide +kernel

theorem rows22250R_1165 : rowsJ2 66 67 53 54 ≤ 6963445345525 := by decide +kernel

theorem rows22250R_1166 : rowsJ2 66 67 54 55 ≤ 7712010071928 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1157
#print axioms SieveCert.rows22250R_1166
