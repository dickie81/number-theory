/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 614–626 of 4715

File 60 of 351: the parts `rows22250R_614` … `rows22250R_626` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 96779 in units of a depth-4 test: row 52 columns 50–50, row 52 columns
51–51, row 52 columns 52–339, row 53 columns 0–15, row 53 columns 16–20, row 53 columns 21–22, row 53 columns 23–23,
row 53 columns 24–24, row 53 columns 25–25, row 53 columns 26–26, row 53 columns 27–27, row 53 columns 28–28, row 53
columns 29–29), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_614 : rowsJ2 52 53 50 51 ≤ 4704021049270 := by decide +kernel

theorem rows22250R_615 : rowsJ2 52 53 51 52 ≤ 6163325948314 := by decide +kernel

theorem rows22250R_616 : rowsJ2 52 53 52 340 ≤ 7564226945643 := by decide +kernel

theorem rows22250R_617 : rowsJ2 53 54 0 16 ≤ 3150523011527 := by decide +kernel

theorem rows22250R_618 : rowsJ2 53 54 16 21 ≤ 1512398431154 := by decide +kernel

theorem rows22250R_619 : rowsJ2 53 54 21 23 ≤ 349916791312 := by decide +kernel

theorem rows22250R_620 : rowsJ2 53 54 23 24 ≤ 134232056012 := by decide +kernel

theorem rows22250R_621 : rowsJ2 53 54 24 25 ≤ 111628686792 := by decide +kernel

theorem rows22250R_622 : rowsJ2 53 54 25 26 ≤ 90486094313 := by decide +kernel

theorem rows22250R_623 : rowsJ2 53 54 26 27 ≤ 75535035997 := by decide +kernel

theorem rows22250R_624 : rowsJ2 53 54 27 28 ≤ 60777716322 := by decide +kernel

theorem rows22250R_625 : rowsJ2 53 54 28 29 ≤ 46162558417 := by decide +kernel

theorem rows22250R_626 : rowsJ2 53 54 29 30 ≤ 31013256316 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_614
#print axioms SieveCert.rows22250R_626
