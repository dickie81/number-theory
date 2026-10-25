/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 561–568 of 4715

File 55 of 351: the parts `rows22250R_561` … `rows22250R_568` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 90332 tests: row 51 columns 28–28, row 51 columns 29–29, row 51 columns
30–30, row 51 columns 31–31, row 51 columns 32–32, row 51 columns 33–33, row 51 columns 34–34, row 51 columns
35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_561 : rowsJ2 51 52 28 29 ≤ 83115331167 := by decide +kernel

theorem rows22250R_562 : rowsJ2 51 52 29 30 ≤ 63574893603 := by decide +kernel

theorem rows22250R_563 : rowsJ2 51 52 30 31 ≤ 47205401451 := by decide +kernel

theorem rows22250R_564 : rowsJ2 51 52 31 32 ≤ 31492974544 := by decide +kernel

theorem rows22250R_565 : rowsJ2 51 52 32 33 ≤ 20160141889 := by decide +kernel

theorem rows22250R_566 : rowsJ2 51 52 33 34 ≤ 10099884457 := by decide +kernel

theorem rows22250R_567 : rowsJ2 51 52 34 35 ≤ 4434730220 := by decide +kernel

theorem rows22250R_568 : rowsJ2 51 52 35 36 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_561
#print axioms SieveCert.rows22250R_568
