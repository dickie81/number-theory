/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4555–4570 of 5066

File 356 of 387: the parts `rows22240R_4555` … `rows22240R_4570` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96557 in units of a depth-4 test: row 161 columns 58–58, row 161
columns 59–59, row 161 columns 60–60, row 161 columns 61–62, row 161 columns 63–65, row 161 columns 66–339, row 162
columns 0–39, row 162 columns 40–42, row 162 columns 43–44, row 162 columns 45–45, row 162 columns 46–46, row 162
columns 47–47, row 162 columns 48–48, row 162 columns 49–49, row 162 columns 50–50, row 162 columns 51–51), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_4555 : rowsJ2 161 162 58 59 ≤ 10190829612641 := by decide +kernel

theorem rows22240R_4556 : rowsJ2 161 162 59 60 ≤ 8876207326960 := by decide +kernel

theorem rows22240R_4557 : rowsJ2 161 162 60 61 ≤ 7660025659324 := by decide +kernel

theorem rows22240R_4558 : rowsJ2 161 162 61 63 ≤ 12053745942382 := by decide +kernel

theorem rows22240R_4559 : rowsJ2 161 162 63 66 ≤ 11296179190829 := by decide +kernel

theorem rows22240R_4560 : rowsJ2 161 162 66 340 ≤ 2591314199824170 := by decide +kernel

theorem rows22240R_4561 : rowsJ2 162 163 0 40 ≤ 10085367462941 := by decide +kernel

theorem rows22240R_4562 : rowsJ2 162 163 40 43 ≤ 15966722961340 := by decide +kernel

theorem rows22240R_4563 : rowsJ2 162 163 43 45 ≤ 15880216789128 := by decide +kernel

theorem rows22240R_4564 : rowsJ2 162 163 45 46 ≤ 9708631611638 := by decide +kernel

theorem rows22240R_4565 : rowsJ2 162 163 46 47 ≤ 10969001192487 := by decide +kernel

theorem rows22240R_4566 : rowsJ2 162 163 47 48 ≤ 12287385216474 := by decide +kernel

theorem rows22240R_4567 : rowsJ2 162 163 48 49 ≤ 13661712772190 := by decide +kernel

theorem rows22240R_4568 : rowsJ2 162 163 49 50 ≤ 15090175308226 := by decide +kernel

theorem rows22240R_4569 : rowsJ2 162 163 50 51 ≤ 16571107045877 := by decide +kernel

theorem rows22240R_4570 : rowsJ2 162 163 51 52 ≤ 18103028459811 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4555
#print axioms SieveCert.rows22240R_4570
