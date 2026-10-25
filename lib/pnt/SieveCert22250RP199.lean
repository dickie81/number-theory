/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2086–2095 of 5796

File 199 of 465: the parts `rows22250R_2086` … `rows22250R_2095` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97870 tests: row 84 columns 53–53, row 84 columns 54–54, row 84 columns
55–55, row 84 columns 56–56, row 84 columns 57–57, row 84 columns 58–58, row 84 columns 59–59, row 84 columns 60–60,
row 84 columns 61–61, row 84 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2086 : rowsJ2 84 85 53 54 ≤ 1104975685824 := by decide +kernel

theorem rows22250R_2087 : rowsJ2 84 85 54 55 ≤ 968038463583 := by decide +kernel

theorem rows22250R_2088 : rowsJ2 84 85 55 56 ≤ 832477801221 := by decide +kernel

theorem rows22250R_2089 : rowsJ2 84 85 56 57 ≤ 741793011995 := by decide +kernel

theorem rows22250R_2090 : rowsJ2 84 85 57 58 ≤ 652003716542 := by decide +kernel

theorem rows22250R_2091 : rowsJ2 84 85 58 59 ≤ 607196154364 := by decide +kernel

theorem rows22250R_2092 : rowsJ2 84 85 59 60 ≤ 516243742040 := by decide +kernel

theorem rows22250R_2093 : rowsJ2 84 85 60 61 ≤ 470816516220 := by decide +kernel

theorem rows22250R_2094 : rowsJ2 84 85 61 62 ≤ 378525651467 := by decide +kernel

theorem rows22250R_2095 : rowsJ2 84 85 62 63 ≤ 332342151629 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2086
#print axioms SieveCert.rows22250R_2095
