/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3473–3489 of 4715

File 268 of 351: the parts `rows22250R_3473` … `rows22250R_3489` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 99717 in units of a depth-4 test: row 130 columns 71–71, row 130
columns 72–72, row 130 columns 73–73, row 130 columns 74–74, row 130 columns 75–76, row 130 columns 77–78, row 130
columns 79–81, row 130 columns 82–85, row 130 columns 86–88, row 130 columns 89–339, row 131 columns 0–23, row 131
columns 24–29, row 131 columns 30–51, row 131 columns 52–54, row 131 columns 55–56, row 131 columns 57–57, row 131
columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_3473 : rowsJ2 130 131 71 72 ≤ 5162597687173 := by decide +kernel

theorem rows22250R_3474 : rowsJ2 130 131 72 73 ≤ 4479076594216 := by decide +kernel

theorem rows22250R_3475 : rowsJ2 130 131 73 74 ≤ 3859392842059 := by decide +kernel

theorem rows22250R_3476 : rowsJ2 130 131 74 75 ≤ 3278700131183 := by decide +kernel

theorem rows22250R_3477 : rowsJ2 130 131 75 77 ≤ 5035876455545 := by decide +kernel

theorem rows22250R_3478 : rowsJ2 130 131 77 79 ≤ 3315931265572 := by decide +kernel

theorem rows22250R_3479 : rowsJ2 130 131 79 82 ≤ 2547092114228 := by decide +kernel

theorem rows22250R_3480 : rowsJ2 130 131 82 86 ≤ 10031795269958 := by decide +kernel

theorem rows22250R_3481 : rowsJ2 130 131 86 89 ≤ 20477589720632 := by decide +kernel

theorem rows22250R_3482 : rowsJ2 130 131 89 340 ≤ 709635790711028 := by decide +kernel

theorem rows22250R_3483 : rowsJ2 131 132 0 24 ≤ 3572880725867 := by decide +kernel

theorem rows22250R_3484 : rowsJ2 131 132 24 30 ≤ 14080299670149 := by decide +kernel

theorem rows22250R_3485 : rowsJ2 131 132 30 52 ≤ 3170548574297 := by decide +kernel

theorem rows22250R_3486 : rowsJ2 131 132 52 55 ≤ 4884359598247 := by decide +kernel

theorem rows22250R_3487 : rowsJ2 131 132 55 57 ≤ 5718039061757 := by decide +kernel

theorem rows22250R_3488 : rowsJ2 131 132 57 58 ≤ 3739789802682 := by decide +kernel

theorem rows22250R_3489 : rowsJ2 131 132 58 59 ≤ 4385441275530 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3473
#print axioms SieveCert.rows22250R_3489
