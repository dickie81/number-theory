/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1345–1356 of 5066

File 129 of 387: the parts `rows22240R_1345` … `rows22240R_1356` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 94606 in units of a depth-4 test: row 69 columns 62–62, row 69 columns
63–63, row 69 columns 64–64, row 69 columns 65–65, row 69 columns 66–66, row 69 columns 67–67, row 69 columns 68–68,
row 69 columns 69–339, row 70 columns 0–17, row 70 columns 18–20, row 70 columns 21–21, row 70 columns 22–22), each
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

theorem rows22240R_1345 : rowsJ2 69 70 62 63 ≤ 5369764102598 := by decide +kernel

theorem rows22240R_1346 : rowsJ2 69 70 63 64 ≤ 5026200075021 := by decide +kernel

theorem rows22240R_1347 : rowsJ2 69 70 64 65 ≤ 4686060427105 := by decide +kernel

theorem rows22240R_1348 : rowsJ2 69 70 65 66 ≤ 4337068129222 := by decide +kernel

theorem rows22240R_1349 : rowsJ2 69 70 66 67 ≤ 3991242443361 := by decide +kernel

theorem rows22240R_1350 : rowsJ2 69 70 67 68 ≤ 3635957488336 := by decide +kernel

theorem rows22240R_1351 : rowsJ2 69 70 68 69 ≤ 3283577267491 := by decide +kernel

theorem rows22240R_1352 : rowsJ2 69 70 69 340 ≤ 2921105026415 := by decide +kernel

theorem rows22240R_1353 : rowsJ2 70 71 0 18 ≤ 1479527213472 := by decide +kernel

theorem rows22240R_1354 : rowsJ2 70 71 18 21 ≤ 30111138304 := by decide +kernel

theorem rows22240R_1355 : rowsJ2 70 71 21 22 ≤ 0 := by decide +kernel

theorem rows22240R_1356 : rowsJ2 70 71 22 23 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1345
#print axioms SieveCert.rows22240R_1356
