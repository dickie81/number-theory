/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3765–3777 of 4715

File 289 of 351: the parts `rows22250R_3765` … `rows22250R_3777` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 99011 in units of a depth-4 test: row 141 columns 61–61, row 141
columns 62–62, row 141 columns 63–63, row 141 columns 64–64, row 141 columns 65–65, row 141 columns 66–66, row 141
columns 67–67, row 141 columns 68–68, row 141 columns 69–69, row 141 columns 70–70, row 141 columns 71–72, row 141
columns 73–75, row 141 columns 76–80), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_3765 : rowsJ2 141 142 61 62 ≤ 12576317941934 := by decide +kernel

theorem rows22250R_3766 : rowsJ2 141 142 62 63 ≤ 12398170610322 := by decide +kernel

theorem rows22250R_3767 : rowsJ2 141 142 63 64 ≤ 11172771265412 := by decide +kernel

theorem rows22250R_3768 : rowsJ2 141 142 64 65 ≤ 10005370283255 := by decide +kernel

theorem rows22250R_3769 : rowsJ2 141 142 65 66 ≤ 8914751420236 := by decide +kernel

theorem rows22250R_3770 : rowsJ2 141 142 66 67 ≤ 7877725073104 := by decide +kernel

theorem rows22250R_3771 : rowsJ2 141 142 67 68 ≤ 6913536497249 := by decide +kernel

theorem rows22250R_3772 : rowsJ2 141 142 68 69 ≤ 5998983786980 := by decide +kernel

theorem rows22250R_3773 : rowsJ2 141 142 69 70 ≤ 5153764246521 := by decide +kernel

theorem rows22250R_3774 : rowsJ2 141 142 70 71 ≤ 4376517008540 := by decide +kernel

theorem rows22250R_3775 : rowsJ2 141 142 71 73 ≤ 6687046289509 := by decide +kernel

theorem rows22250R_3776 : rowsJ2 141 142 73 76 ≤ 5834435585099 := by decide +kernel

theorem rows22250R_3777 : rowsJ2 141 142 76 81 ≤ 2690799644878 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3765
#print axioms SieveCert.rows22250R_3777
