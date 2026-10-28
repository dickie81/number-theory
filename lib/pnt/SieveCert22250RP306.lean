/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4003–4016 of 4715

File 306 of 351: the parts `rows22250R_4003` … `rows22250R_4016` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 98614 in units of a depth-4 test: row 151 columns 49–49, row 151
columns 50–50, row 151 columns 51–51, row 151 columns 52–52, row 151 columns 53–53, row 151 columns 54–54, row 151
columns 55–55, row 151 columns 56–56, row 151 columns 57–57, row 151 columns 58–58, row 151 columns 59–59, row 151
columns 60–60, row 151 columns 61–61, row 151 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4003 : rowsJ2 151 152 49 50 ≤ 7007011287663 := by decide +kernel

theorem rows22250R_4004 : rowsJ2 151 152 50 51 ≤ 8001376046454 := by decide +kernel

theorem rows22250R_4005 : rowsJ2 151 152 51 52 ≤ 9046674030025 := by decide +kernel

theorem rows22250R_4006 : rowsJ2 151 152 52 53 ≤ 10140945343139 := by decide +kernel

theorem rows22250R_4007 : rowsJ2 151 152 53 54 ≤ 11282404376263 := by decide +kernel

theorem rows22250R_4008 : rowsJ2 151 152 54 55 ≤ 12469430787125 := by decide +kernel

theorem rows22250R_4009 : rowsJ2 151 152 55 56 ≤ 13700561359024 := by decide +kernel

theorem rows22250R_4010 : rowsJ2 151 152 56 57 ≤ 14974482681838 := by decide +kernel

theorem rows22250R_4011 : rowsJ2 151 152 57 58 ≤ 14830541763613 := by decide +kernel

theorem rows22250R_4012 : rowsJ2 151 152 58 59 ≤ 13309236555370 := by decide +kernel

theorem rows22250R_4013 : rowsJ2 151 152 59 60 ≤ 11881428412026 := by decide +kernel

theorem rows22250R_4014 : rowsJ2 151 152 60 61 ≤ 10544524839417 := by decide +kernel

theorem rows22250R_4015 : rowsJ2 151 152 61 62 ≤ 9296118029171 := by decide +kernel

theorem rows22250R_4016 : rowsJ2 151 152 62 63 ≤ 8133976100185 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4003
#print axioms SieveCert.rows22250R_4016
