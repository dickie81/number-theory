/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3546–3560 of 5066

File 284 of 387: the parts `rows22240R_3546` … `rows22240R_3560` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99632 in units of a depth-4 test: row 123 columns 80–83, row 123
columns 84–86, row 123 columns 87–88, row 123 columns 89–90, row 123 columns 91–92, row 123 columns 93–339, row 124
columns 0–25, row 124 columns 26–28, row 124 columns 29–31, row 124 columns 32–35, row 124 columns 36–44, row 124
columns 45–56, row 124 columns 57–59, row 124 columns 60–61, row 124 columns 62–62), each a sum of refined costs
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

theorem rows22240R_3546 : rowsJ2 123 124 80 84 ≤ 3105459523956 := by decide +kernel

theorem rows22240R_3547 : rowsJ2 123 124 84 87 ≤ 9833897689198 := by decide +kernel

theorem rows22240R_3548 : rowsJ2 123 124 87 89 ≤ 11653505766951 := by decide +kernel

theorem rows22240R_3549 : rowsJ2 123 124 89 91 ≤ 16779448905251 := by decide +kernel

theorem rows22240R_3550 : rowsJ2 123 124 91 93 ≤ 22878232294687 := by decide +kernel

theorem rows22240R_3551 : rowsJ2 123 124 93 340 ≤ 1103712943581522 := by decide +kernel

theorem rows22240R_3552 : rowsJ2 124 125 0 26 ≤ 2718663763686 := by decide +kernel

theorem rows22240R_3553 : rowsJ2 124 125 26 29 ≤ 12816989490514 := by decide +kernel

theorem rows22240R_3554 : rowsJ2 124 125 29 32 ≤ 20529961713072 := by decide +kernel

theorem rows22240R_3555 : rowsJ2 124 125 32 36 ≤ 15544548927578 := by decide +kernel

theorem rows22240R_3556 : rowsJ2 124 125 36 45 ≤ 6016650537649 := by decide +kernel

theorem rows22240R_3557 : rowsJ2 124 125 45 57 ≤ 2771717471624 := by decide +kernel

theorem rows22240R_3558 : rowsJ2 124 125 57 60 ≤ 5613136618681 := by decide +kernel

theorem rows22240R_3559 : rowsJ2 124 125 60 62 ≤ 6151690717104 := by decide +kernel

theorem rows22240R_3560 : rowsJ2 124 125 62 63 ≤ 3808457923802 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3546
#print axioms SieveCert.rows22240R_3560
