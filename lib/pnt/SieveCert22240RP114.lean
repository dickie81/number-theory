/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1169–1185 of 5066

File 114 of 387: the parts `rows22240R_1169` … `rows22240R_1185` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (17 parts, work 97131 in units of a depth-4 test: row 66 columns 29–29, row 66 columns
30–30, row 66 columns 31–31, row 66 columns 32–32, row 66 columns 33–33, row 66 columns 34–34, row 66 columns 35–35,
row 66 columns 36–36, row 66 columns 37–37, row 66 columns 38–38, row 66 columns 39–39, row 66 columns 40–40, row 66
columns 41–41, row 66 columns 42–42, row 66 columns 43–43, row 66 columns 44–44, row 66 columns 45–45), each a sum
of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1169 : rowsJ2 66 67 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1170 : rowsJ2 66 67 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1171 : rowsJ2 66 67 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1172 : rowsJ2 66 67 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1173 : rowsJ2 66 67 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1174 : rowsJ2 66 67 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1175 : rowsJ2 66 67 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1176 : rowsJ2 66 67 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1177 : rowsJ2 66 67 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1178 : rowsJ2 66 67 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1179 : rowsJ2 66 67 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_1180 : rowsJ2 66 67 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1181 : rowsJ2 66 67 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1182 : rowsJ2 66 67 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1183 : rowsJ2 66 67 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1184 : rowsJ2 66 67 44 45 ≤ 66236347589 := by decide +kernel

theorem rows22240R_1185 : rowsJ2 66 67 45 46 ≤ 193704364403 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1169
#print axioms SieveCert.rows22240R_1185
