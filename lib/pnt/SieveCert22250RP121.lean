/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1350–1361 of 4715

File 121 of 351: the parts `rows22250R_1350` … `rows22250R_1361` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 99842 in units of a depth-4 test: row 70 columns 58–58, row 70 columns
59–59, row 70 columns 60–60, row 70 columns 61–61, row 70 columns 62–62, row 70 columns 63–63, row 70 columns 64–64,
row 70 columns 65–65, row 70 columns 66–66, row 70 columns 67–67, row 70 columns 68–68, row 70 columns 69–69), each
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

theorem rows22250R_1350 : rowsJ2 70 71 58 59 ≤ 4918250885125 := by decide +kernel

theorem rows22250R_1351 : rowsJ2 70 71 59 60 ≤ 4631855036614 := by decide +kernel

theorem rows22250R_1352 : rowsJ2 70 71 60 61 ≤ 4284356558100 := by decide +kernel

theorem rows22250R_1353 : rowsJ2 70 71 61 62 ≤ 3994048803807 := by decide +kernel

theorem rows22250R_1354 : rowsJ2 70 71 62 63 ≤ 3641320984734 := by decide +kernel

theorem rows22250R_1355 : rowsJ2 70 71 63 64 ≤ 3346333591507 := by decide +kernel

theorem rows22250R_1356 : rowsJ2 70 71 64 65 ≤ 2987538292522 := by decide +kernel

theorem rows22250R_1357 : rowsJ2 70 71 65 66 ≤ 2687081174885 := by decide +kernel

theorem rows22250R_1358 : rowsJ2 70 71 66 67 ≤ 2321352971562 := by decide +kernel

theorem rows22250R_1359 : rowsJ2 70 71 67 68 ≤ 2014608362628 := by decide +kernel

theorem rows22250R_1360 : rowsJ2 70 71 68 69 ≤ 1710072391811 := by decide +kernel

theorem rows22250R_1361 : rowsJ2 70 71 69 70 ≤ 1464878057684 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1350
#print axioms SieveCert.rows22250R_1361
