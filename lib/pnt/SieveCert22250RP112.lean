/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1240–1253 of 4715

File 112 of 351: the parts `rows22250R_1240` … `rows22250R_1253` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 96978 in units of a depth-4 test: row 68 columns 34–35, row 68 columns
36–37, row 68 columns 38–39, row 68 columns 40–41, row 68 columns 42–42, row 68 columns 43–43, row 68 columns 44–44,
row 68 columns 45–45, row 68 columns 46–46, row 68 columns 47–47, row 68 columns 48–48, row 68 columns 49–49, row 68
columns 50–50, row 68 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1240 : rowsJ2 68 69 34 36 ≤ 0 := by decide +kernel

theorem rows22250R_1241 : rowsJ2 68 69 36 38 ≤ 0 := by decide +kernel

theorem rows22250R_1242 : rowsJ2 68 69 38 40 ≤ 0 := by decide +kernel

theorem rows22250R_1243 : rowsJ2 68 69 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_1244 : rowsJ2 68 69 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1245 : rowsJ2 68 69 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1246 : rowsJ2 68 69 44 45 ≤ 64142918755 := by decide +kernel

theorem rows22250R_1247 : rowsJ2 68 69 45 46 ≤ 251761106666 := by decide +kernel

theorem rows22250R_1248 : rowsJ2 68 69 46 47 ≤ 751091164444 := by decide +kernel

theorem rows22250R_1249 : rowsJ2 68 69 47 48 ≤ 1491550546148 := by decide +kernel

theorem rows22250R_1250 : rowsJ2 68 69 48 49 ≤ 2203989242840 := by decide +kernel

theorem rows22250R_1251 : rowsJ2 68 69 49 50 ≤ 3014609070026 := by decide +kernel

theorem rows22250R_1252 : rowsJ2 68 69 50 51 ≤ 4000041875121 := by decide +kernel

theorem rows22250R_1253 : rowsJ2 68 69 51 52 ≤ 5009838672740 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1240
#print axioms SieveCert.rows22250R_1253
