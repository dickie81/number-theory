/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 582–587 of 5796

File 62 of 465: the parts `rows22250R_582` … `rows22250R_587` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 90403 tests: row 51 columns 31–31, row 51 columns 32–32, row 51 columns
33–33, row 51 columns 34–34, row 51 columns 35–35, row 51 columns 36–36), each a sum of refined costs (`rows2` or
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

theorem rows22250R_582 : rowsJ2 51 52 31 32 ≤ 103055521743 := by decide +kernel

theorem rows22250R_583 : rowsJ2 51 52 32 33 ≤ 85863056319 := by decide +kernel

theorem rows22250R_584 : rowsJ2 51 52 33 34 ≤ 69783842322 := by decide +kernel

theorem rows22250R_585 : rowsJ2 51 52 34 35 ≤ 52947015843 := by decide +kernel

theorem rows22250R_586 : rowsJ2 51 52 35 36 ≤ 40833617099 := by decide +kernel

theorem rows22250R_587 : rowsJ2 51 52 36 37 ≤ 28803579897 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_582
#print axioms SieveCert.rows22250R_587
