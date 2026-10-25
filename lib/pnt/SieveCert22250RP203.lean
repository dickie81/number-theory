/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2137–2149 of 5796

File 203 of 465: the parts `rows22250R_2137` … `rows22250R_2149` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96579 tests: row 85 columns 56–56, row 85 columns 57–57, row 85 columns
58–58, row 85 columns 59–59, row 85 columns 60–60, row 85 columns 61–61, row 85 columns 62–62, row 85 columns 63–63,
row 85 columns 64–64, row 85 columns 65–65, row 85 columns 66–66, row 85 columns 67–67, row 85 columns 68–68), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2137 : rowsJ2 85 86 56 57 ≤ 463797463731 := by decide +kernel

theorem rows22250R_2138 : rowsJ2 85 86 57 58 ≤ 418632238409 := by decide +kernel

theorem rows22250R_2139 : rowsJ2 85 86 58 59 ≤ 373913701533 := by decide +kernel

theorem rows22250R_2140 : rowsJ2 85 86 59 60 ≤ 328152526201 := by decide +kernel

theorem rows22250R_2141 : rowsJ2 85 86 60 61 ≤ 282804274221 := by decide +kernel

theorem rows22250R_2142 : rowsJ2 85 86 61 62 ≤ 236342591200 := by decide +kernel

theorem rows22250R_2143 : rowsJ2 85 86 62 63 ≤ 190259896175 := by decide +kernel

theorem rows22250R_2144 : rowsJ2 85 86 63 64 ≤ 142990501127 := by decide +kernel

theorem rows22250R_2145 : rowsJ2 85 86 64 65 ≤ 96065718605 := by decide +kernel

theorem rows22250R_2146 : rowsJ2 85 86 65 66 ≤ 47878099597 := by decide +kernel

theorem rows22250R_2147 : rowsJ2 85 86 66 67 ≤ 0 := by decide +kernel

theorem rows22250R_2148 : rowsJ2 85 86 67 68 ≤ 0 := by decide +kernel

theorem rows22250R_2149 : rowsJ2 85 86 68 69 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2137
#print axioms SieveCert.rows22250R_2149
