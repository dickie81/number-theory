/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2127–2136 of 5796

File 202 of 465: the parts `rows22250R_2127` … `rows22250R_2136` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97192 tests: row 85 columns 46–46, row 85 columns 47–47, row 85 columns
48–48, row 85 columns 49–49, row 85 columns 50–50, row 85 columns 51–51, row 85 columns 52–52, row 85 columns 53–53,
row 85 columns 54–54, row 85 columns 55–55), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2127 : rowsJ2 85 86 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2128 : rowsJ2 85 86 47 48 ≤ 91615563453 := by decide +kernel

theorem rows22250R_2129 : rowsJ2 85 86 48 49 ≤ 410606200642 := by decide +kernel

theorem rows22250R_2130 : rowsJ2 85 86 49 50 ≤ 680200967009 := by decide +kernel

theorem rows22250R_2131 : rowsJ2 85 86 50 51 ≤ 771684214941 := by decide +kernel

theorem rows22250R_2132 : rowsJ2 85 86 51 52 ≤ 818623115791 := by decide +kernel

theorem rows22250R_2133 : rowsJ2 85 86 52 53 ≤ 871388971138 := by decide +kernel

theorem rows22250R_2134 : rowsJ2 85 86 53 54 ≤ 781139549992 := by decide +kernel

theorem rows22250R_2135 : rowsJ2 85 86 54 55 ≤ 645095259008 := by decide +kernel

theorem rows22250R_2136 : rowsJ2 85 86 55 56 ≤ 554007796020 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2127
#print axioms SieveCert.rows22250R_2136
