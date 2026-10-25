/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1152–1166 of 5796

File 120 of 465: the parts `rows22250R_1152` … `rows22250R_1166` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99280 tests: row 66 columns 31–31, row 66 columns 32–32, row 66 columns
33–33, row 66 columns 34–34, row 66 columns 35–35, row 66 columns 36–36, row 66 columns 37–37, row 66 columns 38–38,
row 66 columns 39–39, row 66 columns 40–40, row 66 columns 41–41, row 66 columns 42–42, row 66 columns 43–43, row 66
columns 44–44, row 66 columns 45–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1152 : rowsJ2 66 67 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1153 : rowsJ2 66 67 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1154 : rowsJ2 66 67 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1155 : rowsJ2 66 67 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1156 : rowsJ2 66 67 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1157 : rowsJ2 66 67 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1158 : rowsJ2 66 67 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1159 : rowsJ2 66 67 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1160 : rowsJ2 66 67 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1161 : rowsJ2 66 67 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1162 : rowsJ2 66 67 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1163 : rowsJ2 66 67 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1164 : rowsJ2 66 67 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1165 : rowsJ2 66 67 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1166 : rowsJ2 66 67 45 46 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1152
#print axioms SieveCert.rows22250R_1166
