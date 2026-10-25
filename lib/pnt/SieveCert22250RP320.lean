/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4208–4223 of 4715

File 320 of 351: the parts `rows22250R_4208` … `rows22250R_4223` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94929 tests: row 160 columns 54–54, row 160 columns 55–55, row 160 columns
56–56, row 160 columns 57–57, row 160 columns 58–58, row 160 columns 59–60, row 160 columns 61–62, row 160 columns
63–66, row 160 columns 67–339, row 161 columns 0–39, row 161 columns 40–42, row 161 columns 43–44, row 161 columns
45–45, row 161 columns 46–46, row 161 columns 47–47, row 161 columns 48–48), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4208 : rowsJ2 160 161 54 55 ≤ 14760051161713 := by decide +kernel

theorem rows22250R_4209 : rowsJ2 160 161 55 56 ≤ 13132565403722 := by decide +kernel

theorem rows22250R_4210 : rowsJ2 160 161 56 57 ≤ 11611933662948 := by decide +kernel

theorem rows22250R_4211 : rowsJ2 160 161 57 58 ≤ 10195168607811 := by decide +kernel

theorem rows22250R_4212 : rowsJ2 160 161 58 59 ≤ 8879511363516 := by decide +kernel

theorem rows22250R_4213 : rowsJ2 160 161 59 61 ≤ 14203983397401 := by decide +kernel

theorem rows22250R_4214 : rowsJ2 160 161 61 63 ≤ 10095001512637 := by decide +kernel

theorem rows22250R_4215 : rowsJ2 160 161 63 67 ≤ 10759950232804 := by decide +kernel

theorem rows22250R_4216 : rowsJ2 160 161 67 340 ≤ 2630036717190502 := by decide +kernel

theorem rows22250R_4217 : rowsJ2 161 162 0 40 ≤ 10586227802919 := by decide +kernel

theorem rows22250R_4218 : rowsJ2 161 162 40 43 ≤ 15807517007832 := by decide +kernel

theorem rows22250R_4219 : rowsJ2 161 162 43 45 ≤ 15724379257086 := by decide +kernel

theorem rows22250R_4220 : rowsJ2 161 162 45 46 ≤ 9614194037329 := by decide +kernel

theorem rows22250R_4221 : rowsJ2 161 162 46 47 ≤ 10862901182995 := by decide +kernel

theorem rows22250R_4222 : rowsJ2 161 162 47 48 ≤ 12169161609231 := by decide +kernel

theorem rows22250R_4223 : rowsJ2 161 162 48 49 ≤ 13530872027839 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4208
#print axioms SieveCert.rows22250R_4223
