/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1203–1214 of 5066

File 117 of 387: the parts `rows22240R_1203` … `rows22240R_1214` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 96586 in units of a depth-4 test: row 66 columns 63–63, row 66 columns
64–64, row 66 columns 65–65, row 66 columns 66–339, row 67 columns 0–17, row 67 columns 18–20, row 67 columns 21–22,
row 67 columns 23–23, row 67 columns 24–24, row 67 columns 25–25, row 67 columns 26–26, row 67 columns 27–27), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1203 : rowsJ2 66 67 63 64 ≤ 7564229180110 := by decide +kernel

theorem rows22240R_1204 : rowsJ2 66 67 64 65 ≤ 7165070280329 := by decide +kernel

theorem rows22240R_1205 : rowsJ2 66 67 65 66 ≤ 6703273971522 := by decide +kernel

theorem rows22240R_1206 : rowsJ2 66 67 66 340 ≤ 6298037858741 := by decide +kernel

theorem rows22240R_1207 : rowsJ2 67 68 0 18 ≤ 1981565770137 := by decide +kernel

theorem rows22240R_1208 : rowsJ2 67 68 18 21 ≤ 114491669556 := by decide +kernel

theorem rows22240R_1209 : rowsJ2 67 68 21 23 ≤ 25337262340 := by decide +kernel

theorem rows22240R_1210 : rowsJ2 67 68 23 24 ≤ 4209274847 := by decide +kernel

theorem rows22240R_1211 : rowsJ2 67 68 24 25 ≤ 0 := by decide +kernel

theorem rows22240R_1212 : rowsJ2 67 68 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1213 : rowsJ2 67 68 26 27 ≤ 0 := by decide +kernel

theorem rows22240R_1214 : rowsJ2 67 68 27 28 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1203
#print axioms SieveCert.rows22240R_1214
