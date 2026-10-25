/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4967–4977 of 5796

File 409 of 465: the parts `rows22250R_4967` … `rows22250R_4977` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99526 tests: row 161 columns 56–56, row 161 columns 57–57, row 161 columns
58–58, row 161 columns 59–59, row 161 columns 60–60, row 161 columns 61–61, row 161 columns 62–62, row 161 columns
63–63, row 161 columns 64–64, row 161 columns 65–65, row 161 columns 66–66), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4967 : rowsJ2 161 162 56 57 ≤ 10790810702151 := by decide +kernel

theorem rows22250R_4968 : rowsJ2 161 162 57 58 ≤ 11830070089372 := by decide +kernel

theorem rows22250R_4969 : rowsJ2 161 162 58 59 ≤ 12904686914758 := by decide +kernel

theorem rows22250R_4970 : rowsJ2 161 162 59 60 ≤ 14013702382174 := by decide +kernel

theorem rows22250R_4971 : rowsJ2 161 162 60 61 ≤ 13886071573612 := by decide +kernel

theorem rows22250R_4972 : rowsJ2 161 162 61 62 ≤ 12555278071306 := by decide +kernel

theorem rows22250R_4973 : rowsJ2 161 162 62 63 ≤ 11300991240074 := by decide +kernel

theorem rows22250R_4974 : rowsJ2 161 162 63 64 ≤ 10121160733360 := by decide +kernel

theorem rows22250R_4975 : rowsJ2 161 162 64 65 ≤ 9013873862632 := by decide +kernel

theorem rows22250R_4976 : rowsJ2 161 162 65 66 ≤ 7977349261180 := by decide +kernel

theorem rows22250R_4977 : rowsJ2 161 162 66 67 ≤ 7009931097066 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4967
#print axioms SieveCert.rows22250R_4977
