/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5180–5194 of 5796

File 425 of 465: the parts `rows22250R_5180` … `rows22250R_5194` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 93716 tests: row 169 columns 62–62, row 169 columns 63–63, row 169 columns
64–64, row 169 columns 65–66, row 169 columns 67–69, row 169 columns 70–359, row 170 columns 0–41, row 170 columns
42–44, row 170 columns 45–46, row 170 columns 47–47, row 170 columns 48–48, row 170 columns 49–49, row 170 columns
50–50, row 170 columns 51–51, row 170 columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5180 : rowsJ2 169 170 62 63 ≤ 8013876706090 := by decide +kernel

theorem rows22250R_5181 : rowsJ2 169 170 63 64 ≤ 6983638281551 := by decide +kernel

theorem rows22250R_5182 : rowsJ2 169 170 64 65 ≤ 6029578673977 := by decide +kernel

theorem rows22250R_5183 : rowsJ2 169 170 65 67 ≤ 9493792891654 := by decide +kernel

theorem rows22250R_5184 : rowsJ2 169 170 67 70 ≤ 8904382551234 := by decide +kernel

theorem rows22250R_5185 : rowsJ2 169 170 70 360 ≤ 2524671891283347 := by decide +kernel

theorem rows22250R_5186 : rowsJ2 170 171 0 42 ≤ 7964785158204 := by decide +kernel

theorem rows22250R_5187 : rowsJ2 170 171 42 45 ≤ 12647457641692 := by decide +kernel

theorem rows22250R_5188 : rowsJ2 170 171 45 47 ≤ 12604107315837 := by decide +kernel

theorem rows22250R_5189 : rowsJ2 170 171 47 48 ≤ 7714178894321 := by decide +kernel

theorem rows22250R_5190 : rowsJ2 170 171 48 49 ≤ 8721693860384 := by decide +kernel

theorem rows22250R_5191 : rowsJ2 170 171 49 50 ≤ 9776376602299 := by decide +kernel

theorem rows22250R_5192 : rowsJ2 170 171 50 51 ≤ 10876506813099 := by decide +kernel

theorem rows22250R_5193 : rowsJ2 170 171 51 52 ≤ 12020524140252 := by decide +kernel

theorem rows22250R_5194 : rowsJ2 170 171 52 53 ≤ 13207020303058 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5180
#print axioms SieveCert.rows22250R_5194
