/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1077–1091 of 5066

File 106 of 387: the parts `rows22240R_1077` … `rows22240R_1091` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99644 in units of a depth-4 test: row 64 columns 28–28, row 64 columns
29–29, row 64 columns 30–30, row 64 columns 31–31, row 64 columns 32–32, row 64 columns 33–33, row 64 columns 34–34,
row 64 columns 35–35, row 64 columns 36–36, row 64 columns 37–37, row 64 columns 38–38, row 64 columns 39–39, row 64
columns 40–40, row 64 columns 41–41, row 64 columns 42–42), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1077 : rowsJ2 64 65 28 29 ≤ 0 := by decide +kernel

theorem rows22240R_1078 : rowsJ2 64 65 29 30 ≤ 0 := by decide +kernel

theorem rows22240R_1079 : rowsJ2 64 65 30 31 ≤ 0 := by decide +kernel

theorem rows22240R_1080 : rowsJ2 64 65 31 32 ≤ 0 := by decide +kernel

theorem rows22240R_1081 : rowsJ2 64 65 32 33 ≤ 0 := by decide +kernel

theorem rows22240R_1082 : rowsJ2 64 65 33 34 ≤ 0 := by decide +kernel

theorem rows22240R_1083 : rowsJ2 64 65 34 35 ≤ 0 := by decide +kernel

theorem rows22240R_1084 : rowsJ2 64 65 35 36 ≤ 0 := by decide +kernel

theorem rows22240R_1085 : rowsJ2 64 65 36 37 ≤ 0 := by decide +kernel

theorem rows22240R_1086 : rowsJ2 64 65 37 38 ≤ 0 := by decide +kernel

theorem rows22240R_1087 : rowsJ2 64 65 38 39 ≤ 0 := by decide +kernel

theorem rows22240R_1088 : rowsJ2 64 65 39 40 ≤ 0 := by decide +kernel

theorem rows22240R_1089 : rowsJ2 64 65 40 41 ≤ 0 := by decide +kernel

theorem rows22240R_1090 : rowsJ2 64 65 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1091 : rowsJ2 64 65 42 43 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1077
#print axioms SieveCert.rows22240R_1091
