/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1573–1579 of 5796

File 158 of 465: the parts `rows22250R_1573` … `rows22250R_1579` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 92854 tests: row 74 columns 57–57, row 74 columns 58–58, row 74 columns
59–59, row 74 columns 60–60, row 74 columns 61–61, row 74 columns 62–62, row 74 columns 63–63), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1573 : rowsJ2 74 75 57 58 ≤ 5158707717083 := by decide +kernel

theorem rows22250R_1574 : rowsJ2 74 75 58 59 ≤ 5420688718452 := by decide +kernel

theorem rows22250R_1575 : rowsJ2 74 75 59 60 ≤ 5103387482158 := by decide +kernel

theorem rows22250R_1576 : rowsJ2 74 75 60 61 ≤ 4830892703455 := by decide +kernel

theorem rows22250R_1577 : rowsJ2 74 75 61 62 ≤ 4510285945431 := by decide +kernel

theorem rows22250R_1578 : rowsJ2 74 75 62 63 ≤ 4234790232825 := by decide +kernel

theorem rows22250R_1579 : rowsJ2 74 75 63 64 ≤ 3910203141726 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1573
#print axioms SieveCert.rows22250R_1579
