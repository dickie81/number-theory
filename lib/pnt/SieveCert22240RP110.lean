/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1123–1138 of 5066

File 110 of 387: the parts `rows22240R_1123` … `rows22240R_1138` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96568 in units of a depth-4 test: row 65 columns 29–29, row 65 columns
30–30, row 65 columns 31–31, row 65 columns 32–32, row 65 columns 33–33, row 65 columns 34–34, row 65 columns 35–35,
row 65 columns 36–36, row 65 columns 37–37, row 65 columns 38–38, row 65 columns 39–39, row 65 columns 40–40, row 65
columns 41–41, row 65 columns 42–42, row 65 columns 43–43, row 65 columns 44–44), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1123 : rowsJ2 65 66 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1124 : rowsJ2 65 66 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1125 : rowsJ2 65 66 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1126 : rowsJ2 65 66 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1127 : rowsJ2 65 66 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1128 : rowsJ2 65 66 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1129 : rowsJ2 65 66 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1130 : rowsJ2 65 66 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1131 : rowsJ2 65 66 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1132 : rowsJ2 65 66 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1133 : rowsJ2 65 66 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_1134 : rowsJ2 65 66 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1135 : rowsJ2 65 66 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1136 : rowsJ2 65 66 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1137 : rowsJ2 65 66 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1138 : rowsJ2 65 66 44 45 ≤ 66829651776 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1123
#print axioms SieveCert.rows22240R_1138
