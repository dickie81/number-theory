/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3490–3502 of 4715

File 269 of 351: the parts `rows22250R_3490` … `rows22250R_3502` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 95264 tests: row 131 columns 59–59, row 131 columns 60–60, row 131 columns
61–61, row 131 columns 62–62, row 131 columns 63–63, row 131 columns 64–64, row 131 columns 65–65, row 131 columns
66–66, row 131 columns 67–67, row 131 columns 68–68, row 131 columns 69–69, row 131 columns 70–70, row 131 columns
71–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_3490 : rowsJ2 131 132 59 60 ≤ 5072685135264 := by decide +kernel

theorem rows22250R_3491 : rowsJ2 131 132 60 61 ≤ 5778179465682 := by decide +kernel

theorem rows22250R_3492 : rowsJ2 131 132 61 62 ≤ 6436092233287 := by decide +kernel

theorem rows22250R_3493 : rowsJ2 131 132 62 63 ≤ 7024291325405 := by decide +kernel

theorem rows22250R_3494 : rowsJ2 131 132 63 64 ≤ 7564311698724 := by decide +kernel

theorem rows22250R_3495 : rowsJ2 131 132 64 65 ≤ 8033560221899 := by decide +kernel

theorem rows22250R_3496 : rowsJ2 131 132 65 66 ≤ 8453539754795 := by decide +kernel

theorem rows22250R_3497 : rowsJ2 131 132 66 67 ≤ 8801157065858 := by decide +kernel

theorem rows22250R_3498 : rowsJ2 131 132 67 68 ≤ 8486702136422 := by decide +kernel

theorem rows22250R_3499 : rowsJ2 131 132 68 69 ≤ 7578958413610 := by decide +kernel

theorem rows22250R_3500 : rowsJ2 131 132 69 70 ≤ 6740908443367 := by decide +kernel

theorem rows22250R_3501 : rowsJ2 131 132 70 71 ≤ 5948077694848 := by decide +kernel

theorem rows22250R_3502 : rowsJ2 131 132 71 72 ≤ 5221819399484 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3490
#print axioms SieveCert.rows22250R_3502
