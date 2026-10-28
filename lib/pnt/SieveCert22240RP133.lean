/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1393–1405 of 5066

File 133 of 387: the parts `rows22240R_1393` … `rows22240R_1405` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 98542 in units of a depth-4 test: row 70 columns 62–62, row 70 columns
63–63, row 70 columns 64–64, row 70 columns 65–65, row 70 columns 66–66, row 70 columns 67–67, row 70 columns 68–68,
row 70 columns 69–69, row 70 columns 70–339, row 71 columns 0–17, row 71 columns 18–20, row 71 columns 21–21, row 71
columns 22–22), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22240R_1393 : rowsJ2 70 71 62 63 ≤ 4569220182726 := by decide +kernel

theorem rows22240R_1394 : rowsJ2 70 71 63 64 ≤ 4227621522236 := by decide +kernel

theorem rows22240R_1395 : rowsJ2 70 71 64 65 ≤ 3942256592252 := by decide +kernel

theorem rows22240R_1396 : rowsJ2 70 71 65 66 ≤ 3595096755975 := by decide +kernel

theorem rows22240R_1397 : rowsJ2 70 71 66 67 ≤ 3304750781582 := by decide +kernel

theorem rows22240R_1398 : rowsJ2 70 71 67 68 ≤ 2951206844326 := by decide +kernel

theorem rows22240R_1399 : rowsJ2 70 71 68 69 ≤ 2655103404412 := by decide +kernel

theorem rows22240R_1400 : rowsJ2 70 71 69 70 ≤ 2294322683837 := by decide +kernel

theorem rows22240R_1401 : rowsJ2 70 71 70 340 ≤ 1991655359286 := by decide +kernel

theorem rows22240R_1402 : rowsJ2 71 72 0 18 ≤ 1324036614550 := by decide +kernel

theorem rows22240R_1403 : rowsJ2 71 72 18 21 ≤ 12983359927 := by decide +kernel

theorem rows22240R_1404 : rowsJ2 71 72 21 22 ≤ 0 := by decide +kernel

theorem rows22240R_1405 : rowsJ2 71 72 22 23 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1393
#print axioms SieveCert.rows22240R_1405
