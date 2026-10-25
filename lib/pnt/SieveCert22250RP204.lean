/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2150–2164 of 5796

File 204 of 465: the parts `rows22250R_2150` … `rows22250R_2164` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95718 tests: row 85 columns 69–69, row 85 columns 70–70, row 85 columns
71–72, row 85 columns 73–74, row 85 columns 75–76, row 85 columns 77–79, row 85 columns 80–81, row 85 columns 82–83,
row 85 columns 84–84, row 85 columns 85–359, row 86 columns 0–17, row 86 columns 18–19, row 86 columns 20–21, row 86
columns 22–23, row 86 columns 24–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2150 : rowsJ2 85 86 69 70 ≤ 0 := by decide +kernel

theorem rows22250R_2151 : rowsJ2 85 86 70 71 ≤ 0 := by decide +kernel

theorem rows22250R_2152 : rowsJ2 85 86 71 73 ≤ 0 := by decide +kernel

theorem rows22250R_2153 : rowsJ2 85 86 73 75 ≤ 0 := by decide +kernel

theorem rows22250R_2154 : rowsJ2 85 86 75 77 ≤ 0 := by decide +kernel

theorem rows22250R_2155 : rowsJ2 85 86 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_2156 : rowsJ2 85 86 80 82 ≤ 227606359297 := by decide +kernel

theorem rows22250R_2157 : rowsJ2 85 86 82 84 ≤ 1307041872591 := by decide +kernel

theorem rows22250R_2158 : rowsJ2 85 86 84 85 ≤ 1445105418722 := by decide +kernel

theorem rows22250R_2159 : rowsJ2 85 86 85 360 ≤ 1724870406732 := by decide +kernel

theorem rows22250R_2160 : rowsJ2 86 87 0 18 ≤ 43968285067 := by decide +kernel

theorem rows22250R_2161 : rowsJ2 86 87 18 20 ≤ 7995524208 := by decide +kernel

theorem rows22250R_2162 : rowsJ2 86 87 20 22 ≤ 4319602869 := by decide +kernel

theorem rows22250R_2163 : rowsJ2 86 87 22 24 ≤ 713822204 := by decide +kernel

theorem rows22250R_2164 : rowsJ2 86 87 24 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2150
#print axioms SieveCert.rows22250R_2164
