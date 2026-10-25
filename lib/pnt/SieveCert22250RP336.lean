/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4010–4025 of 5796

File 336 of 465: the parts `rows22250R_4010` … `rows22250R_4025` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97560 tests: row 129 columns 97–98, row 129 columns 99–359, row 130 columns
0–26, row 130 columns 27–29, row 130 columns 30–31, row 130 columns 32–34, row 130 columns 35–39, row 130 columns
40–55, row 130 columns 56–60, row 130 columns 61–62, row 130 columns 63–63, row 130 columns 64–64, row 130 columns
65–65, row 130 columns 66–66, row 130 columns 67–67, row 130 columns 68–68), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4010 : rowsJ2 129 130 97 99 ≤ 19555880139735 := by decide +kernel

theorem rows22250R_4011 : rowsJ2 129 130 99 360 ≤ 996866000341488 := by decide +kernel

theorem rows22250R_4012 : rowsJ2 130 131 0 27 ≤ 1665365983525 := by decide +kernel

theorem rows22250R_4013 : rowsJ2 130 131 27 30 ≤ 10412562254297 := by decide +kernel

theorem rows22250R_4014 : rowsJ2 130 131 30 32 ≤ 11733789695195 := by decide +kernel

theorem rows22250R_4015 : rowsJ2 130 131 32 35 ≤ 11897427260889 := by decide +kernel

theorem rows22250R_4016 : rowsJ2 130 131 35 40 ≤ 8314453766992 := by decide +kernel

theorem rows22250R_4017 : rowsJ2 130 131 40 56 ≤ 631648583402 := by decide +kernel

theorem rows22250R_4018 : rowsJ2 130 131 56 61 ≤ 3222835047270 := by decide +kernel

theorem rows22250R_4019 : rowsJ2 130 131 61 63 ≤ 3321232255822 := by decide +kernel

theorem rows22250R_4020 : rowsJ2 130 131 63 64 ≤ 2244321209061 := by decide +kernel

theorem rows22250R_4021 : rowsJ2 130 131 64 65 ≤ 2642431176562 := by decide +kernel

theorem rows22250R_4022 : rowsJ2 130 131 65 66 ≤ 2983346493149 := by decide +kernel

theorem rows22250R_4023 : rowsJ2 130 131 66 67 ≤ 3284826226916 := by decide +kernel

theorem rows22250R_4024 : rowsJ2 130 131 67 68 ≤ 3528155592265 := by decide +kernel

theorem rows22250R_4025 : rowsJ2 130 131 68 69 ≤ 3731080468475 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4010
#print axioms SieveCert.rows22250R_4025
