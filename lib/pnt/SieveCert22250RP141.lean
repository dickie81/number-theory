/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1378–1386 of 5796

File 141 of 465: the parts `rows22250R_1378` … `rows22250R_1386` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 98347 tests: row 70 columns 64–64, row 70 columns 65–65, row 70 columns
66–66, row 70 columns 67–67, row 70 columns 68–68, row 70 columns 69–69, row 70 columns 70–359, row 71 columns 0–18,
row 71 columns 19–21), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_1378 : rowsJ2 70 71 64 65 ≤ 6515284075778 := by decide +kernel

theorem rows22250R_1379 : rowsJ2 70 71 65 66 ≤ 6092339638296 := by decide +kernel

theorem rows22250R_1380 : rowsJ2 70 71 66 67 ≤ 5715136881126 := by decide +kernel

theorem rows22250R_1381 : rowsJ2 70 71 67 68 ≤ 5341458688640 := by decide +kernel

theorem rows22250R_1382 : rowsJ2 70 71 68 69 ≤ 5013514802871 := by decide +kernel

theorem rows22250R_1383 : rowsJ2 70 71 69 70 ≤ 4688543445495 := by decide +kernel

theorem rows22250R_1384 : rowsJ2 70 71 70 360 ≤ 4409392491592 := by decide +kernel

theorem rows22250R_1385 : rowsJ2 71 72 0 19 ≤ 1040678811368 := by decide +kernel

theorem rows22250R_1386 : rowsJ2 71 72 19 22 ≤ 3372529861 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1378
#print axioms SieveCert.rows22250R_1386
