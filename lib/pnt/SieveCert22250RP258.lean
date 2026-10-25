/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3321–3336 of 4715

File 258 of 351: the parts `rows22250R_3321` … `rows22250R_3336` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96313 tests: row 125 columns 34–51, row 125 columns 52–56, row 125 columns
57–58, row 125 columns 59–60, row 125 columns 61–61, row 125 columns 62–62, row 125 columns 63–63, row 125 columns
64–64, row 125 columns 65–65, row 125 columns 66–66, row 125 columns 67–67, row 125 columns 68–68, row 125 columns
69–69, row 125 columns 70–70, row 125 columns 71–71, row 125 columns 72–72), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3321 : rowsJ2 125 126 34 52 ≤ 3890543151137 := by decide +kernel

theorem rows22250R_3322 : rowsJ2 125 126 52 57 ≤ 4145415673087 := by decide +kernel

theorem rows22250R_3323 : rowsJ2 125 126 57 59 ≤ 4260891334054 := by decide +kernel

theorem rows22250R_3324 : rowsJ2 125 126 59 61 ≤ 6282486958674 := by decide +kernel

theorem rows22250R_3325 : rowsJ2 125 126 61 62 ≤ 3888794673912 := by decide +kernel

theorem rows22250R_3326 : rowsJ2 125 126 62 63 ≤ 4299009599705 := by decide +kernel

theorem rows22250R_3327 : rowsJ2 125 126 63 64 ≤ 4659488310667 := by decide +kernel

theorem rows22250R_3328 : rowsJ2 125 126 64 65 ≤ 4946703121391 := by decide +kernel

theorem rows22250R_3329 : rowsJ2 125 126 65 66 ≤ 5182758948835 := by decide +kernel

theorem rows22250R_3330 : rowsJ2 125 126 66 67 ≤ 5343607524283 := by decide +kernel

theorem rows22250R_3331 : rowsJ2 125 126 67 68 ≤ 5451304864278 := by decide +kernel

theorem rows22250R_3332 : rowsJ2 125 126 68 69 ≤ 5481231810979 := by decide +kernel

theorem rows22250R_3333 : rowsJ2 125 126 69 70 ≤ 5455373392205 := by decide +kernel

theorem rows22250R_3334 : rowsJ2 125 126 70 71 ≤ 5023773557941 := by decide +kernel

theorem rows22250R_3335 : rowsJ2 125 126 71 72 ≤ 4302801077548 := by decide +kernel

theorem rows22250R_3336 : rowsJ2 125 126 72 73 ≤ 3623205473659 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3321
#print axioms SieveCert.rows22250R_3336
