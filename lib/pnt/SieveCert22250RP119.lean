/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1327–1341 of 4715

File 119 of 351: the parts `rows22250R_1327` … `rows22250R_1341` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 96853 in units of a depth-4 test: row 70 columns 29–29, row 70 columns
30–30, row 70 columns 31–32, row 70 columns 33–34, row 70 columns 35–36, row 70 columns 37–38, row 70 columns 39–40,
row 70 columns 41–42, row 70 columns 43–43, row 70 columns 44–44, row 70 columns 45–45, row 70 columns 46–46, row 70
columns 47–47, row 70 columns 48–48, row 70 columns 49–49), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1327 : rowsJ2 70 71 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1328 : rowsJ2 70 71 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1329 : rowsJ2 70 71 31 33 ≤ 0 := by decide +kernel

theorem rows22250R_1330 : rowsJ2 70 71 33 35 ≤ 0 := by decide +kernel

theorem rows22250R_1331 : rowsJ2 70 71 35 37 ≤ 0 := by decide +kernel

theorem rows22250R_1332 : rowsJ2 70 71 37 39 ≤ 0 := by decide +kernel

theorem rows22250R_1333 : rowsJ2 70 71 39 41 ≤ 0 := by decide +kernel

theorem rows22250R_1334 : rowsJ2 70 71 41 43 ≤ 0 := by decide +kernel

theorem rows22250R_1335 : rowsJ2 70 71 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1336 : rowsJ2 70 71 44 45 ≤ 63046759782 := by decide +kernel

theorem rows22250R_1337 : rowsJ2 70 71 45 46 ≤ 247458680121 := by decide +kernel

theorem rows22250R_1338 : rowsJ2 70 71 46 47 ≤ 738255525905 := by decide +kernel

theorem rows22250R_1339 : rowsJ2 70 71 47 48 ≤ 1466060959026 := by decide +kernel

theorem rows22250R_1340 : rowsJ2 70 71 48 49 ≤ 2166324561635 := by decide +kernel

theorem rows22250R_1341 : rowsJ2 70 71 49 50 ≤ 2963091445816 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1327
#print axioms SieveCert.rows22250R_1341
