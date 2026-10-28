/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2112–2126 of 4715

File 176 of 351: the parts `rows22250R_2112` … `rows22250R_2126` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 95926 in units of a depth-4 test: row 88 columns 45–45, row 88 columns
46–46, row 88 columns 47–47, row 88 columns 48–48, row 88 columns 49–49, row 88 columns 50–50, row 88 columns 51–51,
row 88 columns 52–52, row 88 columns 53–53, row 88 columns 54–54, row 88 columns 55–55, row 88 columns 56–56, row 88
columns 57–58, row 88 columns 59–60, row 88 columns 61–62), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2112 : rowsJ2 88 89 45 46 ≤ 12485362651209 := by decide +kernel

theorem rows22250R_2113 : rowsJ2 88 89 46 47 ≤ 8494935108170 := by decide +kernel

theorem rows22250R_2114 : rowsJ2 88 89 47 48 ≤ 3771534148885 := by decide +kernel

theorem rows22250R_2115 : rowsJ2 88 89 48 49 ≤ 0 := by decide +kernel

theorem rows22250R_2116 : rowsJ2 88 89 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_2117 : rowsJ2 88 89 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2118 : rowsJ2 88 89 51 52 ≤ 0 := by decide +kernel

theorem rows22250R_2119 : rowsJ2 88 89 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2120 : rowsJ2 88 89 53 54 ≤ 0 := by decide +kernel

theorem rows22250R_2121 : rowsJ2 88 89 54 55 ≤ 0 := by decide +kernel

theorem rows22250R_2122 : rowsJ2 88 89 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2123 : rowsJ2 88 89 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2124 : rowsJ2 88 89 57 59 ≤ 0 := by decide +kernel

theorem rows22250R_2125 : rowsJ2 88 89 59 61 ≤ 0 := by decide +kernel

theorem rows22250R_2126 : rowsJ2 88 89 61 63 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2112
#print axioms SieveCert.rows22250R_2126
