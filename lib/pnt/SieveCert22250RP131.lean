/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1484–1493 of 4715

File 131 of 351: the parts `rows22250R_1484` … `rows22250R_1493` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 95760 tests: row 73 columns 53–53, row 73 columns 54–54, row 73 columns
55–55, row 73 columns 56–56, row 73 columns 57–57, row 73 columns 58–58, row 73 columns 59–59, row 73 columns 60–60,
row 73 columns 61–61, row 73 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1484 : rowsJ2 73 74 53 54 ≤ 4271009660691 := by decide +kernel

theorem rows22250R_1485 : rowsJ2 73 74 54 55 ≤ 3920105012077 := by decide +kernel

theorem rows22250R_1486 : rowsJ2 73 74 55 56 ≤ 3573044624211 := by decide +kernel

theorem rows22250R_1487 : rowsJ2 73 74 56 57 ≤ 3282794219977 := by decide +kernel

theorem rows22250R_1488 : rowsJ2 73 74 57 58 ≤ 2995611884085 := by decide +kernel

theorem rows22250R_1489 : rowsJ2 73 74 58 59 ≤ 2765229595963 := by decide +kernel

theorem rows22250R_1490 : rowsJ2 73 74 59 60 ≤ 2537228005858 := by decide +kernel

theorem rows22250R_1491 : rowsJ2 73 74 60 61 ≤ 2303486881446 := by decide +kernel

theorem rows22250R_1492 : rowsJ2 73 74 61 62 ≤ 2071944222822 := by decide +kernel

theorem rows22250R_1493 : rowsJ2 73 74 62 63 ≤ 1834258222161 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1484
#print axioms SieveCert.rows22250R_1493
