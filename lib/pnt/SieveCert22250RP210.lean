/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2231–2243 of 5796

File 210 of 465: the parts `rows22250R_2231` … `rows22250R_2243` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 96579 tests: row 87 columns 54–54, row 87 columns 55–55, row 87 columns
56–56, row 87 columns 57–57, row 87 columns 58–58, row 87 columns 59–59, row 87 columns 60–60, row 87 columns 61–61,
row 87 columns 62–62, row 87 columns 63–63, row 87 columns 64–64, row 87 columns 65–65, row 87 columns 66–66), each
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

theorem rows22250R_2231 : rowsJ2 87 88 54 55 ≤ 91083291339 := by decide +kernel

theorem rows22250R_2232 : rowsJ2 87 88 55 56 ≤ 45346253947 := by decide +kernel

theorem rows22250R_2233 : rowsJ2 87 88 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2234 : rowsJ2 87 88 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2235 : rowsJ2 87 88 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2236 : rowsJ2 87 88 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_2237 : rowsJ2 87 88 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_2238 : rowsJ2 87 88 61 62 ≤ 0 := by decide +kernel

theorem rows22250R_2239 : rowsJ2 87 88 62 63 ≤ 0 := by decide +kernel

theorem rows22250R_2240 : rowsJ2 87 88 63 64 ≤ 0 := by decide +kernel

theorem rows22250R_2241 : rowsJ2 87 88 64 65 ≤ 0 := by decide +kernel

theorem rows22250R_2242 : rowsJ2 87 88 65 66 ≤ 0 := by decide +kernel

theorem rows22250R_2243 : rowsJ2 87 88 66 67 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2231
#print axioms SieveCert.rows22250R_2243
