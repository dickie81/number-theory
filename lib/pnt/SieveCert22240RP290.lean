/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3637–3651 of 5066

File 290 of 387: the parts `rows22240R_3637` … `rows22240R_3651` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 94427 in units of a depth-4 test: row 126 columns 86–88, row 126
columns 89–90, row 126 columns 91–339, row 127 columns 0–25, row 127 columns 26–28, row 127 columns 29–32, row 127
columns 33–41, row 127 columns 42–55, row 127 columns 56–57, row 127 columns 58–59, row 127 columns 60–60, row 127
columns 61–61, row 127 columns 62–62, row 127 columns 63–63, row 127 columns 64–64), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3637 : rowsJ2 126 127 86 89 ≤ 18841600539099 := by decide +kernel

theorem rows22240R_3638 : rowsJ2 126 127 89 91 ≤ 19728580573805 := by decide +kernel

theorem rows22240R_3639 : rowsJ2 126 127 91 340 ≤ 991769387155973 := by decide +kernel

theorem rows22240R_3640 : rowsJ2 127 128 0 26 ≤ 5031742204571 := by decide +kernel

theorem rows22240R_3641 : rowsJ2 127 128 26 29 ≤ 15204595526494 := by decide +kernel

theorem rows22240R_3642 : rowsJ2 127 128 29 33 ≤ 15871872833476 := by decide +kernel

theorem rows22240R_3643 : rowsJ2 127 128 33 42 ≤ 7763787199280 := by decide +kernel

theorem rows22240R_3644 : rowsJ2 127 128 42 56 ≤ 3538424795449 := by decide +kernel

theorem rows22240R_3645 : rowsJ2 127 128 56 58 ≤ 3869093818374 := by decide +kernel

theorem rows22240R_3646 : rowsJ2 127 128 58 60 ≤ 5868577944498 := by decide +kernel

theorem rows22240R_3647 : rowsJ2 127 128 60 61 ≤ 3792216277845 := by decide +kernel

theorem rows22240R_3648 : rowsJ2 127 128 61 62 ≤ 4396524775070 := by decide +kernel

theorem rows22240R_3649 : rowsJ2 127 128 62 63 ≤ 4953499429642 := by decide +kernel

theorem rows22240R_3650 : rowsJ2 127 128 63 64 ≤ 5440920239349 := by decide +kernel

theorem rows22240R_3651 : rowsJ2 127 128 64 65 ≤ 5880142722510 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3637
#print axioms SieveCert.rows22240R_3651
