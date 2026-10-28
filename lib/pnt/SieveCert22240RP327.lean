/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4143–4156 of 5066

File 327 of 387: the parts `rows22240R_4143` … `rows22240R_4156` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 97782 in units of a depth-4 test: row 144 columns 62–62, row 144
columns 63–63, row 144 columns 64–64, row 144 columns 65–65, row 144 columns 66–66, row 144 columns 67–67, row 144
columns 68–68, row 144 columns 69–69, row 144 columns 70–70, row 144 columns 71–72, row 144 columns 73–75, row 144
columns 76–80, row 144 columns 81–339, row 145 columns 0–27), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4143 : rowsJ2 144 145 62 63 ≤ 12968890470371 := by decide +kernel

theorem rows22240R_4144 : rowsJ2 144 145 63 64 ≤ 11643475126859 := by decide +kernel

theorem rows22240R_4145 : rowsJ2 144 145 64 65 ≤ 10398404940833 := by decide +kernel

theorem rows22240R_4146 : rowsJ2 144 145 65 66 ≤ 9231640392009 := by decide +kernel

theorem rows22240R_4147 : rowsJ2 144 145 66 67 ≤ 8141282467129 := by decide +kernel

theorem rows22240R_4148 : rowsJ2 144 145 67 68 ≤ 7125566027825 := by decide +kernel

theorem rows22240R_4149 : rowsJ2 144 145 68 69 ≤ 6182848989532 := by decide +kernel

theorem rows22240R_4150 : rowsJ2 144 145 69 70 ≤ 5311612026494 := by decide +kernel

theorem rows22240R_4151 : rowsJ2 144 145 70 71 ≤ 4510458181700 := by decide +kernel

theorem rows22240R_4152 : rowsJ2 144 145 71 73 ≤ 6891477792751 := by decide +kernel

theorem rows22240R_4153 : rowsJ2 144 145 73 76 ≤ 6012528334111 := by decide +kernel

theorem rows22240R_4154 : rowsJ2 144 145 76 81 ≤ 2773037510805 := by decide +kernel

theorem rows22240R_4155 : rowsJ2 144 145 81 340 ≤ 1360700730516533 := by decide +kernel

theorem rows22240R_4156 : rowsJ2 145 146 0 28 ≤ 2027828483592 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4143
#print axioms SieveCert.rows22240R_4156
