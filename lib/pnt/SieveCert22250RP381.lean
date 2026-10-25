/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4610–4625 of 5796

File 381 of 465: the parts `rows22250R_4610` … `rows22250R_4625` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94832 tests: row 148 columns 75–75, row 148 columns 76–76, row 148 columns
77–77, row 148 columns 78–79, row 148 columns 80–82, row 148 columns 83–87, row 148 columns 88–359, row 149 columns
0–23, row 149 columns 24–49, row 149 columns 50–52, row 149 columns 53–54, row 149 columns 55–55, row 149 columns
56–56, row 149 columns 57–57, row 149 columns 58–58, row 149 columns 59–59), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4610 : rowsJ2 148 149 75 76 ≤ 4010454465249 := by decide +kernel

theorem rows22250R_4611 : rowsJ2 148 149 76 77 ≤ 3407037647289 := by decide +kernel

theorem rows22250R_4612 : rowsJ2 148 149 77 78 ≤ 2854997378435 := by decide +kernel

theorem rows22250R_4613 : rowsJ2 148 149 78 80 ≤ 4255565807529 := by decide +kernel

theorem rows22250R_4614 : rowsJ2 148 149 80 83 ≤ 3486525163353 := by decide +kernel

theorem rows22250R_4615 : rowsJ2 148 149 83 88 ≤ 2538031074961 := by decide +kernel

theorem rows22250R_4616 : rowsJ2 148 149 88 360 ≤ 824740151088672 := by decide +kernel

theorem rows22250R_4617 : rowsJ2 149 150 0 24 ≤ 1895049664520 := by decide +kernel

theorem rows22250R_4618 : rowsJ2 149 150 24 50 ≤ 2370217992407 := by decide +kernel

theorem rows22250R_4619 : rowsJ2 149 150 50 53 ≤ 5184818400451 := by decide +kernel

theorem rows22250R_4620 : rowsJ2 149 150 53 55 ≤ 5880330752398 := by decide +kernel

theorem rows22250R_4621 : rowsJ2 149 150 55 56 ≤ 3797842277457 := by decide +kernel

theorem rows22250R_4622 : rowsJ2 149 150 56 57 ≤ 4423359188218 := by decide +kernel

theorem rows22250R_4623 : rowsJ2 149 150 57 58 ≤ 5087132626464 := by decide +kernel

theorem rows22250R_4624 : rowsJ2 149 150 58 59 ≤ 5787667866938 := by decide +kernel

theorem rows22250R_4625 : rowsJ2 149 150 59 60 ≤ 6523579122505 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4610
#print axioms SieveCert.rows22250R_4625
