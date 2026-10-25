/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5337–5352 of 5796

File 436 of 465: the parts `rows22250R_5337` … `rows22250R_5352` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96574 tests: row 176 columns 54–54, row 176 columns 55–55, row 176 columns
56–56, row 176 columns 57–57, row 176 columns 58–58, row 176 columns 59–59, row 176 columns 60–60, row 176 columns
61–62, row 176 columns 63–359, row 177 columns 0–39, row 177 columns 40–41, row 177 columns 42–43, row 177 columns
44–44, row 177 columns 45–45, row 177 columns 46–46, row 177 columns 47–47), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5337 : rowsJ2 176 177 54 55 ≤ 15484022343106 := by decide +kernel

theorem rows22250R_5338 : rowsJ2 176 177 55 56 ≤ 13895264171781 := by decide +kernel

theorem rows22250R_5339 : rowsJ2 176 177 56 57 ≤ 12404434180700 := by decide +kernel

theorem rows22250R_5340 : rowsJ2 176 177 57 58 ≤ 11008739792627 := by decide +kernel

theorem rows22250R_5341 : rowsJ2 176 177 58 59 ≤ 9705592992741 := by decide +kernel

theorem rows22250R_5342 : rowsJ2 176 177 59 60 ≤ 8492600311003 := by decide +kernel

theorem rows22250R_5343 : rowsJ2 176 177 60 61 ≤ 7367553757908 := by decide +kernel

theorem rows22250R_5344 : rowsJ2 176 177 61 63 ≤ 11701768873867 := by decide +kernel

theorem rows22250R_5345 : rowsJ2 176 177 63 360 ≤ 2556490458480077 := by decide +kernel

theorem rows22250R_5346 : rowsJ2 177 178 0 40 ≤ 11497712858938 := by decide +kernel

theorem rows22250R_5347 : rowsJ2 177 178 40 42 ≤ 11391105947214 := by decide +kernel

theorem rows22250R_5348 : rowsJ2 177 178 42 44 ≤ 15394403743397 := by decide +kernel

theorem rows22250R_5349 : rowsJ2 177 178 44 45 ≤ 9343686171516 := by decide +kernel

theorem rows22250R_5350 : rowsJ2 177 178 45 46 ≤ 10514047396817 := by decide +kernel

theorem rows22250R_5351 : rowsJ2 177 178 46 47 ≤ 11736340577418 := by decide +kernel

theorem rows22250R_5352 : rowsJ2 177 178 47 48 ≤ 13008728887746 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5337
#print axioms SieveCert.rows22250R_5352
