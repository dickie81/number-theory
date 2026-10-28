/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3547–3559 of 4715

File 273 of 351: the parts `rows22250R_3547` … `rows22250R_3559` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 99568 in units of a depth-4 test: row 133 columns 60–60, row 133
columns 61–61, row 133 columns 62–62, row 133 columns 63–63, row 133 columns 64–64, row 133 columns 65–65, row 133
columns 66–66, row 133 columns 67–67, row 133 columns 68–68, row 133 columns 69–69, row 133 columns 70–70, row 133
columns 71–71, row 133 columns 72–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_3547 : rowsJ2 133 134 60 61 ≤ 6740661350093 := by decide +kernel

theorem rows22250R_3548 : rowsJ2 133 134 61 62 ≤ 7459974872065 := by decide +kernel

theorem rows22250R_3549 : rowsJ2 133 134 62 63 ≤ 8110371808497 := by decide +kernel

theorem rows22250R_3550 : rowsJ2 133 134 63 64 ≤ 8713201408738 := by decide +kernel

theorem rows22250R_3551 : rowsJ2 133 134 64 65 ≤ 9246175725685 := by decide +kernel

theorem rows22250R_3552 : rowsJ2 133 134 65 66 ≤ 9730613749193 := by decide +kernel

theorem rows22250R_3553 : rowsJ2 133 134 66 67 ≤ 9436946241911 := by decide +kernel

theorem rows22250R_3554 : rowsJ2 133 134 67 68 ≤ 8478707827960 := by decide +kernel

theorem rows22250R_3555 : rowsJ2 133 134 68 69 ≤ 7569449294063 := by decide +kernel

theorem rows22250R_3556 : rowsJ2 133 134 69 70 ≤ 6729814585653 := by decide +kernel

theorem rows22250R_3557 : rowsJ2 133 134 70 71 ≤ 5935584591601 := by decide +kernel

theorem rows22250R_3558 : rowsJ2 133 134 71 72 ≤ 5207859971836 := by decide +kernel

theorem rows22250R_3559 : rowsJ2 133 134 72 73 ≤ 4522322811269 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3547
#print axioms SieveCert.rows22250R_3559
