/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4994–5004 of 5796

File 411 of 465: the parts `rows22250R_4994` … `rows22250R_5004` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 97407 tests: row 162 columns 56–56, row 162 columns 57–57, row 162 columns
58–58, row 162 columns 59–59, row 162 columns 60–60, row 162 columns 61–61, row 162 columns 62–62, row 162 columns
63–63, row 162 columns 64–64, row 162 columns 65–65, row 162 columns 66–66), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4994 : rowsJ2 162 163 56 57 ≤ 11504255492797 := by decide +kernel

theorem rows22250R_4995 : rowsJ2 162 163 57 58 ≤ 12578370296643 := by decide +kernel

theorem rows22250R_4996 : rowsJ2 162 163 58 59 ≤ 13687875215908 := by decide +kernel

theorem rows22250R_4997 : rowsJ2 162 163 59 60 ≤ 14831854193588 := by decide +kernel

theorem rows22250R_4998 : rowsJ2 162 163 60 61 ≤ 13438548587800 := by decide +kernel

theorem rows22250R_4999 : rowsJ2 162 163 61 62 ≤ 12124272355669 := by decide +kernel

theorem rows22250R_5000 : rowsJ2 162 163 62 63 ≤ 10886846647825 := by decide +kernel

theorem rows22250R_5001 : rowsJ2 162 163 63 64 ≤ 9724237972692 := by decide +kernel

theorem rows22250R_5002 : rowsJ2 162 163 64 65 ≤ 8634551311647 := by decide +kernel

theorem rows22250R_5003 : rowsJ2 162 163 65 66 ≤ 7616023828524 := by decide +kernel

theorem rows22250R_5004 : rowsJ2 162 163 66 67 ≤ 6667019131765 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4994
#print axioms SieveCert.rows22250R_5004
