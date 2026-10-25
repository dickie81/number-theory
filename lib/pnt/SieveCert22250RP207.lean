/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2189–2203 of 5796

File 207 of 465: the parts `rows22250R_2189` … `rows22250R_2203` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95593 tests: row 86 columns 60–60, row 86 columns 61–61, row 86 columns
62–62, row 86 columns 63–63, row 86 columns 64–64, row 86 columns 65–65, row 86 columns 66–66, row 86 columns 67–67,
row 86 columns 68–68, row 86 columns 69–69, row 86 columns 70–71, row 86 columns 72–73, row 86 columns 74–75, row 86
columns 76–78, row 86 columns 79–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2189 : rowsJ2 86 87 60 61 ≤ 141113083487 := by decide +kernel

theorem rows22250R_2190 : rowsJ2 86 87 61 62 ≤ 94762717299 := by decide +kernel

theorem rows22250R_2191 : rowsJ2 86 87 62 63 ≤ 94943754553 := by decide +kernel

theorem rows22250R_2192 : rowsJ2 86 87 63 64 ≤ 47835496961 := by decide +kernel

theorem rows22250R_2193 : rowsJ2 86 87 64 65 ≤ 47943160933 := by decide +kernel

theorem rows22250R_2194 : rowsJ2 86 87 65 66 ≤ 0 := by decide +kernel

theorem rows22250R_2195 : rowsJ2 86 87 66 67 ≤ 0 := by decide +kernel

theorem rows22250R_2196 : rowsJ2 86 87 67 68 ≤ 0 := by decide +kernel

theorem rows22250R_2197 : rowsJ2 86 87 68 69 ≤ 0 := by decide +kernel

theorem rows22250R_2198 : rowsJ2 86 87 69 70 ≤ 0 := by decide +kernel

theorem rows22250R_2199 : rowsJ2 86 87 70 72 ≤ 0 := by decide +kernel

theorem rows22250R_2200 : rowsJ2 86 87 72 74 ≤ 0 := by decide +kernel

theorem rows22250R_2201 : rowsJ2 86 87 74 76 ≤ 0 := by decide +kernel

theorem rows22250R_2202 : rowsJ2 86 87 76 79 ≤ 0 := by decide +kernel

theorem rows22250R_2203 : rowsJ2 86 87 79 82 ≤ 225930302847 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2189
#print axioms SieveCert.rows22250R_2203
