/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3519–3531 of 4715

File 271 of 351: the parts `rows22250R_3519` … `rows22250R_3531` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 97723 in units of a depth-4 test: row 132 columns 60–60, row 132
columns 61–61, row 132 columns 62–62, row 132 columns 63–63, row 132 columns 64–64, row 132 columns 65–65, row 132
columns 66–66, row 132 columns 67–67, row 132 columns 68–68, row 132 columns 69–69, row 132 columns 70–70, row 132
columns 71–71, row 132 columns 72–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3519 : rowsJ2 132 133 60 61 ≤ 6239851821949 := by decide +kernel

theorem rows22250R_3520 : rowsJ2 132 133 61 62 ≤ 6928341735612 := by decide +kernel

theorem rows22250R_3521 : rowsJ2 132 133 62 63 ≤ 7547509432469 := by decide +kernel

theorem rows22250R_3522 : rowsJ2 132 133 63 64 ≤ 8118796013984 := by decide +kernel

theorem rows22250R_3523 : rowsJ2 132 133 64 65 ≤ 8619761281517 := by decide +kernel

theorem rows22250R_3524 : rowsJ2 132 133 65 66 ≤ 9071815103363 := by decide +kernel

theorem rows22250R_3525 : rowsJ2 132 133 66 67 ≤ 9452020804194 := by decide +kernel

theorem rows22250R_3526 : rowsJ2 132 133 67 68 ≤ 8494681055164 := by decide +kernel

theorem rows22250R_3527 : rowsJ2 132 133 68 69 ≤ 7586230929115 := by decide +kernel

theorem rows22250R_3528 : rowsJ2 132 133 69 70 ≤ 6747438583886 := by decide +kernel

theorem rows22250R_3529 : rowsJ2 132 133 70 71 ≤ 5953957946110 := by decide +kernel

theorem rows22250R_3530 : rowsJ2 132 133 71 72 ≤ 5227015287473 := by decide +kernel

theorem rows22250R_3531 : rowsJ2 132 133 72 73 ≤ 4542164073990 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3519
#print axioms SieveCert.rows22250R_3531
