/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4366–4378 of 5066

File 343 of 387: the parts `rows22240R_4366` … `rows22240R_4378` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 97429 in units of a depth-4 test: row 153 columns 54–54, row 153
columns 55–55, row 153 columns 56–56, row 153 columns 57–57, row 153 columns 58–58, row 153 columns 59–59, row 153
columns 60–60, row 153 columns 61–61, row 153 columns 62–62, row 153 columns 63–63, row 153 columns 64–64, row 153
columns 65–66, row 153 columns 67–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4366 : rowsJ2 153 154 54 55 ≤ 13413019102316 := by decide +kernel

theorem rows22240R_4367 : rowsJ2 153 154 55 56 ≤ 14698160219947 := by decide +kernel

theorem rows22240R_4368 : rowsJ2 153 154 56 57 ≤ 16026505537375 := by decide +kernel

theorem rows22240R_4369 : rowsJ2 153 154 57 58 ≤ 15872043903690 := by decide +kernel

theorem rows22240R_4370 : rowsJ2 153 154 58 59 ≤ 14277281147928 := by decide +kernel

theorem rows22240R_4371 : rowsJ2 153 154 59 60 ≤ 12778956181507 := by decide +kernel

theorem rows22240R_4372 : rowsJ2 153 154 60 61 ≤ 11374340032275 := by decide +kernel

theorem rows22240R_4373 : rowsJ2 153 154 61 62 ≤ 10060898666864 := by decide +kernel

theorem rows22240R_4374 : rowsJ2 153 154 62 63 ≤ 8836278414336 := by decide +kernel

theorem rows22240R_4375 : rowsJ2 153 154 63 64 ≤ 7698297525638 := by decide +kernel

theorem rows22240R_4376 : rowsJ2 153 154 64 65 ≤ 6644931909004 := by decide +kernel

theorem rows22240R_4377 : rowsJ2 153 154 65 67 ≤ 10459080651977 := by decide +kernel

theorem rows22240R_4378 : rowsJ2 153 154 67 69 ≤ 7217394558742 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4366
#print axioms SieveCert.rows22240R_4378
