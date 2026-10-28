/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3608–3621 of 5066

File 288 of 387: the parts `rows22240R_3608` … `rows22240R_3621` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 94182 in units of a depth-4 test: row 125 columns 87–88, row 125
columns 89–90, row 125 columns 91–339, row 126 columns 0–25, row 126 columns 26–28, row 126 columns 29–32, row 126
columns 33–39, row 126 columns 40–55, row 126 columns 56–58, row 126 columns 59–60, row 126 columns 61–61, row 126
columns 62–62, row 126 columns 63–63, row 126 columns 64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22240R_3608 : rowsJ2 125 126 87 89 ≤ 13059422563252 := by decide +kernel

theorem rows22240R_3609 : rowsJ2 125 126 89 91 ≤ 18688983943225 := by decide +kernel

theorem rows22240R_3610 : rowsJ2 125 126 91 340 ≤ 1008959469701685 := by decide +kernel

theorem rows22240R_3611 : rowsJ2 126 127 0 26 ≤ 4256209435408 := by decide +kernel

theorem rows22240R_3612 : rowsJ2 126 127 26 29 ≤ 15283599329069 := by decide +kernel

theorem rows22240R_3613 : rowsJ2 126 127 29 33 ≤ 18690211855945 := by decide +kernel

theorem rows22240R_3614 : rowsJ2 126 127 33 40 ≤ 10415591951085 := by decide +kernel

theorem rows22240R_3615 : rowsJ2 126 127 40 56 ≤ 2852645038611 := by decide +kernel

theorem rows22240R_3616 : rowsJ2 126 127 56 59 ≤ 5773521981527 := by decide +kernel

theorem rows22240R_3617 : rowsJ2 126 127 59 61 ≤ 6348203258683 := by decide +kernel

theorem rows22240R_3618 : rowsJ2 126 127 61 62 ≤ 4028809822376 := by decide +kernel

theorem rows22240R_3619 : rowsJ2 126 127 62 63 ≤ 4557275878465 := by decide +kernel

theorem rows22240R_3620 : rowsJ2 126 127 63 64 ≤ 5015827493484 := by decide +kernel

theorem rows22240R_3621 : rowsJ2 126 127 64 65 ≤ 5425926508183 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3608
#print axioms SieveCert.rows22240R_3621
