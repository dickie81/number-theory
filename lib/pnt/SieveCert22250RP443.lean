/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5441–5456 of 5796

File 443 of 465: the parts `rows22250R_5441` … `rows22250R_5456` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95139 tests: row 181 columns 53–53, row 181 columns 54–54, row 181 columns
55–55, row 181 columns 56–56, row 181 columns 57–58, row 181 columns 59–359, row 182 columns 0–37, row 182 columns
38–39, row 182 columns 40–41, row 182 columns 42–42, row 182 columns 43–43, row 182 columns 44–44, row 182 columns
45–45, row 182 columns 46–46, row 182 columns 47–47, row 182 columns 48–48), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5441 : rowsJ2 181 182 53 54 ≤ 14423451551972 := by decide +kernel

theorem rows22250R_5442 : rowsJ2 181 182 54 55 ≤ 12835260517169 := by decide +kernel

theorem rows22250R_5443 : rowsJ2 181 182 55 56 ≤ 11351030355560 := by decide +kernel

theorem rows22250R_5444 : rowsJ2 181 182 56 57 ≤ 9967875875438 := by decide +kernel

theorem rows22250R_5445 : rowsJ2 181 182 57 59 ≤ 16177498582221 := by decide +kernel

theorem rows22250R_5446 : rowsJ2 181 182 59 360 ≤ 2618427767623436 := by decide +kernel

theorem rows22250R_5447 : rowsJ2 182 183 0 38 ≤ 10505626520466 := by decide +kernel

theorem rows22250R_5448 : rowsJ2 182 183 38 40 ≤ 12997090834318 := by decide +kernel

theorem rows22250R_5449 : rowsJ2 182 183 40 42 ≤ 18197114672984 := by decide +kernel

theorem rows22250R_5450 : rowsJ2 182 183 42 43 ≤ 10954935016137 := by decide +kernel

theorem rows22250R_5451 : rowsJ2 182 183 43 44 ≤ 12270267706542 := by decide +kernel

theorem rows22250R_5452 : rowsJ2 182 183 44 45 ≤ 13641218092389 := by decide +kernel

theorem rows22250R_5453 : rowsJ2 182 183 45 46 ≤ 15065901919560 := by decide +kernel

theorem rows22250R_5454 : rowsJ2 182 183 46 47 ≤ 16542646989303 := by decide +kernel

theorem rows22250R_5455 : rowsJ2 182 183 47 48 ≤ 18069983440029 := by decide +kernel

theorem rows22250R_5456 : rowsJ2 182 183 48 49 ≤ 19646635237004 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5441
#print axioms SieveCert.rows22250R_5456
