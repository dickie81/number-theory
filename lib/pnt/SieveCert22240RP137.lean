/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1442–1454 of 5066

File 137 of 387: the parts `rows22240R_1442` … `rows22240R_1454` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 96640 in units of a depth-4 test: row 71 columns 62–62, row 71 columns
63–63, row 71 columns 64–64, row 71 columns 65–65, row 71 columns 66–66, row 71 columns 67–67, row 71 columns 68–68,
row 71 columns 69–69, row 71 columns 70–70, row 71 columns 71–339, row 72 columns 0–17, row 72 columns 18–20, row 72
columns 21–21), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1442 : rowsJ2 71 72 62 63 ≤ 3774419583948 := by decide +kernel

theorem rows22240R_1443 : rowsJ2 71 72 63 64 ≤ 3487674289762 := by decide +kernel

theorem rows22240R_1444 : rowsJ2 71 72 64 65 ≤ 3203632500849 := by decide +kernel

theorem rows22240R_1445 : rowsJ2 71 72 65 66 ≤ 2912015083460 := by decide +kernel

theorem rows22240R_1446 : rowsJ2 71 72 66 67 ≤ 2622883256193 := by decide +kernel

theorem rows22240R_1447 : rowsJ2 71 72 67 68 ≤ 2325662888862 := by decide +kernel

theorem rows22240R_1448 : rowsJ2 71 72 68 69 ≤ 2030705863940 := by decide +kernel

theorem rows22240R_1449 : rowsJ2 71 72 69 70 ≤ 1727124387766 := by decide +kernel

theorem rows22240R_1450 : rowsJ2 71 72 70 71 ≤ 1425577706538 := by decide +kernel

theorem rows22240R_1451 : rowsJ2 71 72 71 340 ≤ 1182546459624 := by decide +kernel

theorem rows22240R_1452 : rowsJ2 72 73 0 18 ≤ 1173993550369 := by decide +kernel

theorem rows22240R_1453 : rowsJ2 72 73 18 21 ≤ 4343765064 := by decide +kernel

theorem rows22240R_1454 : rowsJ2 72 73 21 22 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1442
#print axioms SieveCert.rows22240R_1454
