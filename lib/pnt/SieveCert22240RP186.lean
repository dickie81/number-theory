/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2117–2130 of 5066

File 186 of 387: the parts `rows22240R_2117` … `rows22240R_2130` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98348 in units of a depth-4 test: row 85 columns 83–83, row 85 columns
84–84, row 85 columns 85–339, row 86 columns 0–16, row 86 columns 17–19, row 86 columns 20–21, row 86 columns 22–23,
row 86 columns 24–26, row 86 columns 27–30, row 86 columns 31–34, row 86 columns 35–37, row 86 columns 38–39, row 86
columns 40–40, row 86 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2117 : rowsJ2 85 86 83 84 ≤ 2927202110954 := by decide +kernel

theorem rows22240R_2118 : rowsJ2 85 86 84 85 ≤ 3852059803430 := by decide +kernel

theorem rows22240R_2119 : rowsJ2 85 86 85 340 ≤ 4929278095373 := by decide +kernel

theorem rows22240R_2120 : rowsJ2 86 87 0 17 ≤ 56899937290 := by decide +kernel

theorem rows22240R_2121 : rowsJ2 86 87 17 20 ≤ 5861323479 := by decide +kernel

theorem rows22240R_2122 : rowsJ2 86 87 20 22 ≤ 0 := by decide +kernel

theorem rows22240R_2123 : rowsJ2 86 87 22 24 ≤ 0 := by decide +kernel

theorem rows22240R_2124 : rowsJ2 86 87 24 27 ≤ 0 := by decide +kernel

theorem rows22240R_2125 : rowsJ2 86 87 27 31 ≤ 0 := by decide +kernel

theorem rows22240R_2126 : rowsJ2 86 87 31 35 ≤ 1047171071822 := by decide +kernel

theorem rows22240R_2127 : rowsJ2 86 87 35 38 ≤ 8087559418065 := by decide +kernel

theorem rows22240R_2128 : rowsJ2 86 87 38 40 ≤ 10596264221083 := by decide +kernel

theorem rows22240R_2129 : rowsJ2 86 87 40 41 ≤ 6944005667701 := by decide +kernel

theorem rows22240R_2130 : rowsJ2 86 87 41 42 ≤ 8204856627009 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2117
#print axioms SieveCert.rows22240R_2130
