/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1247–1263 of 5796

File 129 of 465: the parts `rows22250R_1247` … `rows22250R_1263` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98309 tests: row 68 columns 32–32, row 68 columns 33–33, row 68 columns
34–34, row 68 columns 35–35, row 68 columns 36–36, row 68 columns 37–37, row 68 columns 38–38, row 68 columns 39–39,
row 68 columns 40–40, row 68 columns 41–41, row 68 columns 42–42, row 68 columns 43–43, row 68 columns 44–44, row 68
columns 45–45, row 68 columns 46–46, row 68 columns 47–47, row 68 columns 48–48), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1247 : rowsJ2 68 69 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1248 : rowsJ2 68 69 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1249 : rowsJ2 68 69 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1250 : rowsJ2 68 69 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1251 : rowsJ2 68 69 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1252 : rowsJ2 68 69 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1253 : rowsJ2 68 69 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1254 : rowsJ2 68 69 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1255 : rowsJ2 68 69 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1256 : rowsJ2 68 69 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1257 : rowsJ2 68 69 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1258 : rowsJ2 68 69 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1259 : rowsJ2 68 69 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_1260 : rowsJ2 68 69 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_1261 : rowsJ2 68 69 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_1262 : rowsJ2 68 69 47 48 ≤ 104836965782 := by decide +kernel

theorem rows22250R_1263 : rowsJ2 68 69 48 49 ≤ 469862396563 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1247
#print axioms SieveCert.rows22250R_1263
