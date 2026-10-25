/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4525–4537 of 5796

File 374 of 465: the parts `rows22250R_4525` … `rows22250R_4537` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 91779 tests: row 146 columns 0–23, row 146 columns 24–47, row 146 columns
48–53, row 146 columns 54–55, row 146 columns 56–56, row 146 columns 57–57, row 146 columns 58–58, row 146 columns
59–59, row 146 columns 60–60, row 146 columns 61–61, row 146 columns 62–62, row 146 columns 63–63, row 146 columns
64–64), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4525 : rowsJ2 146 147 0 24 ≤ 2928202714353 := by decide +kernel

theorem rows22250R_4526 : rowsJ2 146 147 24 48 ≤ 1668663751796 := by decide +kernel

theorem rows22250R_4527 : rowsJ2 146 147 48 54 ≤ 5909512260475 := by decide +kernel

theorem rows22250R_4528 : rowsJ2 146 147 54 56 ≤ 5122408573149 := by decide +kernel

theorem rows22250R_4529 : rowsJ2 146 147 56 57 ≤ 3351360798398 := by decide +kernel

theorem rows22250R_4530 : rowsJ2 146 147 57 58 ≤ 3930821867031 := by decide +kernel

theorem rows22250R_4531 : rowsJ2 146 147 58 59 ≤ 4547787600090 := by decide +kernel

theorem rows22250R_4532 : rowsJ2 146 147 59 60 ≤ 5200781497772 := by decide +kernel

theorem rows22250R_4533 : rowsJ2 146 147 60 61 ≤ 5888431581589 := by decide +kernel

theorem rows22250R_4534 : rowsJ2 146 147 61 62 ≤ 6609464938835 := by decide +kernel

theorem rows22250R_4535 : rowsJ2 146 147 62 63 ≤ 7362702695435 := by decide +kernel

theorem rows22250R_4536 : rowsJ2 146 147 63 64 ≤ 8147055389386 := by decide +kernel

theorem rows22250R_4537 : rowsJ2 146 147 64 65 ≤ 8928550840407 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4525
#print axioms SieveCert.rows22250R_4537
