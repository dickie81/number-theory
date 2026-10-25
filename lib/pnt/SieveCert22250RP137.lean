/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1332–1344 of 5796

File 137 of 465: the parts `rows22250R_1332` … `rows22250R_1344` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97878 tests: row 69 columns 68–68, row 69 columns 69–359, row 70 columns
0–18, row 70 columns 19–21, row 70 columns 22–22, row 70 columns 23–23, row 70 columns 24–24, row 70 columns 25–25,
row 70 columns 26–26, row 70 columns 27–27, row 70 columns 28–28, row 70 columns 29–29, row 70 columns 30–30), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1332 : rowsJ2 69 70 68 69 ≤ 5779198785157 := by decide +kernel

theorem rows22250R_1333 : rowsJ2 69 70 69 360 ≤ 5452541391998 := by decide +kernel

theorem rows22250R_1334 : rowsJ2 70 71 0 19 ≤ 1169699804377 := by decide +kernel

theorem rows22250R_1335 : rowsJ2 70 71 19 22 ≤ 10086379023 := by decide +kernel

theorem rows22250R_1336 : rowsJ2 70 71 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1337 : rowsJ2 70 71 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1338 : rowsJ2 70 71 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1339 : rowsJ2 70 71 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1340 : rowsJ2 70 71 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_1341 : rowsJ2 70 71 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_1342 : rowsJ2 70 71 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_1343 : rowsJ2 70 71 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1344 : rowsJ2 70 71 30 31 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1332
#print axioms SieveCert.rows22250R_1344
