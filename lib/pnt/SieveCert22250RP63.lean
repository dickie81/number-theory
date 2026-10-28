/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 649–660 of 4715

File 63 of 351: the parts `rows22250R_649` … `rows22250R_660` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 89930 in units of a depth-4 test: row 53 columns 52–52, row 53 columns
53–339, row 54 columns 0–15, row 54 columns 16–20, row 54 columns 21–22, row 54 columns 23–23, row 54 columns 24–24,
row 54 columns 25–25, row 54 columns 26–26, row 54 columns 27–27, row 54 columns 28–28, row 54 columns 29–29), each
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

theorem rows22250R_649 : rowsJ2 53 54 52 53 ≤ 7488608984651 := by decide +kernel

theorem rows22250R_650 : rowsJ2 53 54 53 340 ≤ 8967090776954 := by decide +kernel

theorem rows22250R_651 : rowsJ2 54 55 0 16 ≤ 3069737432185 := by decide +kernel

theorem rows22250R_652 : rowsJ2 54 55 16 21 ≤ 1317042801455 := by decide +kernel

theorem rows22250R_653 : rowsJ2 54 55 21 23 ≤ 296850463811 := by decide +kernel

theorem rows22250R_654 : rowsJ2 54 55 23 24 ≤ 112101990657 := by decide +kernel

theorem rows22250R_655 : rowsJ2 54 55 24 25 ≤ 89628223386 := by decide +kernel

theorem rows22250R_656 : rowsJ2 54 55 25 26 ≤ 72782461248 := by decide +kernel

theorem rows22250R_657 : rowsJ2 54 55 26 27 ≤ 57887692639 := by decide +kernel

theorem rows22250R_658 : rowsJ2 54 55 27 28 ≤ 45013887551 := by decide +kernel

theorem rows22250R_659 : rowsJ2 54 55 28 29 ≤ 30460660081 := by decide +kernel

theorem rows22250R_660 : rowsJ2 54 55 29 30 ≤ 19677996134 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_649
#print axioms SieveCert.rows22250R_660
