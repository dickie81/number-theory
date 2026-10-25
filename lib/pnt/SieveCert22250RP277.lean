/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3604–3616 of 4715

File 277 of 351: the parts `rows22250R_3604` … `rows22250R_3616` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 98894 tests: row 135 columns 61–61, row 135 columns 62–62, row 135 columns
63–63, row 135 columns 64–64, row 135 columns 65–65, row 135 columns 66–66, row 135 columns 67–67, row 135 columns
68–68, row 135 columns 69–69, row 135 columns 70–70, row 135 columns 71–71, row 135 columns 72–72, row 135 columns
73–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_3604 : rowsJ2 135 136 61 62 ≤ 8579783707452 := by decide +kernel

theorem rows22250R_3605 : rowsJ2 135 136 62 63 ≤ 9294106860733 := by decide +kernel

theorem rows22250R_3606 : rowsJ2 135 136 63 64 ≤ 9961532016275 := by decide +kernel

theorem rows22250R_3607 : rowsJ2 135 136 64 65 ≤ 10560074331774 := by decide +kernel

theorem rows22250R_3608 : rowsJ2 135 136 65 66 ≤ 10307972669301 := by decide +kernel

theorem rows22250R_3609 : rowsJ2 135 136 66 67 ≤ 9275090117545 := by decide +kernel

theorem rows22250R_3610 : rowsJ2 135 136 67 68 ≤ 8315270621287 := by decide +kernel

theorem rows22250R_3611 : rowsJ2 135 136 68 69 ≤ 7404604344313 := by decide +kernel

theorem rows22250R_3612 : rowsJ2 135 136 69 70 ≤ 6563490911976 := by decide +kernel

theorem rows22250R_3613 : rowsJ2 135 136 70 71 ≤ 5767960972949 := by decide +kernel

theorem rows22250R_3614 : rowsJ2 135 136 71 72 ≤ 5038868133485 := by decide +kernel

theorem rows22250R_3615 : rowsJ2 135 136 72 73 ≤ 4352147515792 := by decide +kernel

theorem rows22250R_3616 : rowsJ2 135 136 73 74 ≤ 3729104707101 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3604
#print axioms SieveCert.rows22250R_3616
