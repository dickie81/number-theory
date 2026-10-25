/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5168–5179 of 5796

File 424 of 465: the parts `rows22250R_5168` … `rows22250R_5179` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 96994 tests: row 169 columns 50–50, row 169 columns 51–51, row 169 columns
52–52, row 169 columns 53–53, row 169 columns 54–54, row 169 columns 55–55, row 169 columns 56–56, row 169 columns
57–57, row 169 columns 58–58, row 169 columns 59–59, row 169 columns 60–60, row 169 columns 61–61), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5168 : rowsJ2 169 170 50 51 ≤ 10127489134498 := by decide +kernel

theorem rows22250R_5169 : rowsJ2 169 170 51 52 ≤ 11230573803886 := by decide +kernel

theorem rows22250R_5170 : rowsJ2 169 170 52 53 ≤ 12376140375144 := by decide +kernel

theorem rows22250R_5171 : rowsJ2 169 170 53 54 ≤ 13562872212171 := by decide +kernel

theorem rows22250R_5172 : rowsJ2 169 170 54 55 ≤ 14789590723748 := by decide +kernel

theorem rows22250R_5173 : rowsJ2 169 170 55 56 ≤ 16055249538499 := by decide +kernel

theorem rows22250R_5174 : rowsJ2 169 170 56 57 ≤ 15903496795112 := by decide +kernel

theorem rows22250R_5175 : rowsJ2 169 170 57 58 ≤ 14374147893545 := by decide +kernel

theorem rows22250R_5176 : rowsJ2 169 170 58 59 ≤ 12933789172812 := by decide +kernel

theorem rows22250R_5177 : rowsJ2 169 170 59 60 ≤ 11579872146164 := by decide +kernel

theorem rows22250R_5178 : rowsJ2 169 170 60 61 ≤ 10310024431310 := by decide +kernel

theorem rows22250R_5179 : rowsJ2 169 170 61 62 ≤ 9122041083519 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5168
#print axioms SieveCert.rows22250R_5179
