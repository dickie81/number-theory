/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1250–1261 of 5066

File 121 of 387: the parts `rows22240R_1250` … `rows22240R_1261` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 96831 in units of a depth-4 test: row 67 columns 63–63, row 67 columns
64–64, row 67 columns 65–65, row 67 columns 66–66, row 67 columns 67–339, row 68 columns 0–17, row 68 columns 18–20,
row 68 columns 21–22, row 68 columns 23–23, row 68 columns 24–24, row 68 columns 25–25, row 68 columns 26–26), each
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

theorem rows22240R_1250 : rowsJ2 67 68 63 64 ≤ 6693997530847 := by decide +kernel

theorem rows22240R_1251 : rowsJ2 67 68 64 65 ≤ 6297381257158 := by decide +kernel

theorem rows22240R_1252 : rowsJ2 67 68 65 66 ≤ 5890672250256 := by decide +kernel

theorem rows22240R_1253 : rowsJ2 67 68 66 67 ≤ 5487838123259 := by decide +kernel

theorem rows22240R_1254 : rowsJ2 67 68 67 340 ≤ 5074212115450 := by decide +kernel

theorem rows22240R_1255 : rowsJ2 68 69 0 18 ≤ 1810287005050 := by decide +kernel

theorem rows22240R_1256 : rowsJ2 68 69 18 21 ≤ 80920256519 := by decide +kernel

theorem rows22240R_1257 : rowsJ2 68 69 21 23 ≤ 12735038986 := by decide +kernel

theorem rows22240R_1258 : rowsJ2 68 69 23 24 ≤ 0 := by decide +kernel

theorem rows22240R_1259 : rowsJ2 68 69 24 25 ≤ 0 := by decide +kernel

theorem rows22240R_1260 : rowsJ2 68 69 25 26 ≤ 0 := by decide +kernel

theorem rows22240R_1261 : rowsJ2 68 69 26 27 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1250
#print axioms SieveCert.rows22240R_1261
