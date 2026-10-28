/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3577–3592 of 5066

File 286 of 387: the parts `rows22240R_3577` … `rows22240R_3592` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97773 in units of a depth-4 test: row 124 columns 85–87, row 124
columns 88–89, row 124 columns 90–91, row 124 columns 92–339, row 125 columns 0–25, row 125 columns 26–28, row 125
columns 29–31, row 125 columns 32–36, row 125 columns 37–52, row 125 columns 53–57, row 125 columns 58–59, row 125
columns 60–60, row 125 columns 61–61, row 125 columns 62–62, row 125 columns 63–63, row 125 columns 64–64), each a
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

theorem rows22240R_3577 : rowsJ2 124 125 85 88 ≤ 13507333012936 := by decide +kernel

theorem rows22240R_3578 : rowsJ2 124 125 88 90 ≤ 14932855190411 := by decide +kernel

theorem rows22240R_3579 : rowsJ2 124 125 90 92 ≤ 20798201360617 := by decide +kernel

theorem rows22240R_3580 : rowsJ2 124 125 92 340 ≤ 1097631191209875 := by decide +kernel

theorem rows22240R_3581 : rowsJ2 125 126 0 26 ≤ 3485252056149 := by decide +kernel

theorem rows22240R_3582 : rowsJ2 125 126 26 29 ≤ 14050452627293 := by decide +kernel

theorem rows22240R_3583 : rowsJ2 125 126 29 32 ≤ 17699410774490 := by decide +kernel

theorem rows22240R_3584 : rowsJ2 125 126 32 37 ≤ 14948139374908 := by decide +kernel

theorem rows22240R_3585 : rowsJ2 125 126 37 53 ≤ 2704817094361 := by decide +kernel

theorem rows22240R_3586 : rowsJ2 125 126 53 58 ≤ 4838757503727 := by decide +kernel

theorem rows22240R_3587 : rowsJ2 125 126 58 60 ≤ 4689383429649 := by decide +kernel

theorem rows22240R_3588 : rowsJ2 125 126 60 61 ≤ 3117324320118 := by decide +kernel

theorem rows22240R_3589 : rowsJ2 125 126 61 62 ≤ 3665458182592 := by decide +kernel

theorem rows22240R_3590 : rowsJ2 125 126 62 63 ≤ 4165843752840 := by decide +kernel

theorem rows22240R_3591 : rowsJ2 125 126 63 64 ≤ 4595950844162 := by decide +kernel

theorem rows22240R_3592 : rowsJ2 125 126 64 65 ≤ 4977367860133 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3577
#print axioms SieveCert.rows22240R_3592
