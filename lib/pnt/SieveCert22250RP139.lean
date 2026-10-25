/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1363–1371 of 5796

File 139 of 465: the parts `rows22250R_1363` … `rows22250R_1371` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 95143 tests: row 70 columns 49–49, row 70 columns 50–50, row 70 columns
51–51, row 70 columns 52–52, row 70 columns 53–53, row 70 columns 54–54, row 70 columns 55–55, row 70 columns 56–56,
row 70 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1363 : rowsJ2 70 71 49 50 ≤ 860338246429 := by decide +kernel

theorem rows22250R_1364 : rowsJ2 70 71 50 51 ≤ 1293974155111 := by decide +kernel

theorem rows22250R_1365 : rowsJ2 70 71 51 52 ≤ 1862671536022 := by decide +kernel

theorem rows22250R_1366 : rowsJ2 70 71 52 53 ≤ 2669596770344 := by decide +kernel

theorem rows22250R_1367 : rowsJ2 70 71 53 54 ≤ 3497381896560 := by decide +kernel

theorem rows22250R_1368 : rowsJ2 70 71 54 55 ≤ 4265869266515 := by decide +kernel

theorem rows22250R_1369 : rowsJ2 70 71 55 56 ≤ 5014520313057 := by decide +kernel

theorem rows22250R_1370 : rowsJ2 70 71 56 57 ≤ 5836723234720 := by decide +kernel

theorem rows22250R_1371 : rowsJ2 70 71 57 58 ≤ 6529308214990 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1363
#print axioms SieveCert.rows22250R_1371
