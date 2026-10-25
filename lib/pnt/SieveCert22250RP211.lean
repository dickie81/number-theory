/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2244–2259 of 5796

File 211 of 465: the parts `rows22250R_2244` … `rows22250R_2259` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97446 tests: row 87 columns 67–67, row 87 columns 68–68, row 87 columns
69–70, row 87 columns 71–72, row 87 columns 73–74, row 87 columns 75–77, row 87 columns 78–80, row 87 columns 81–82,
row 87 columns 83–83, row 87 columns 84–84, row 87 columns 85–85, row 87 columns 86–86, row 87 columns 87–359, row
88 columns 0–16, row 88 columns 17–18, row 88 columns 19–20), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_2244 : rowsJ2 87 88 67 68 ≤ 0 := by decide +kernel

theorem rows22250R_2245 : rowsJ2 87 88 68 69 ≤ 0 := by decide +kernel

theorem rows22250R_2246 : rowsJ2 87 88 69 71 ≤ 0 := by decide +kernel

theorem rows22250R_2247 : rowsJ2 87 88 71 73 ≤ 0 := by decide +kernel

theorem rows22250R_2248 : rowsJ2 87 88 73 75 ≤ 0 := by decide +kernel

theorem rows22250R_2249 : rowsJ2 87 88 75 78 ≤ 0 := by decide +kernel

theorem rows22250R_2250 : rowsJ2 87 88 78 81 ≤ 56242635608 := by decide +kernel

theorem rows22250R_2251 : rowsJ2 87 88 81 83 ≤ 517078062828 := by decide +kernel

theorem rows22250R_2252 : rowsJ2 87 88 83 84 ≤ 772721818219 := by decide +kernel

theorem rows22250R_2253 : rowsJ2 87 88 84 85 ≤ 1170660134088 := by decide +kernel

theorem rows22250R_2254 : rowsJ2 87 88 85 86 ≤ 1435679044655 := by decide +kernel

theorem rows22250R_2255 : rowsJ2 87 88 86 87 ≤ 1768857559704 := by decide +kernel

theorem rows22250R_2256 : rowsJ2 87 88 87 360 ≤ 2198637727282 := by decide +kernel

theorem rows22250R_2257 : rowsJ2 88 89 0 17 ≤ 15940519661 := by decide +kernel

theorem rows22250R_2258 : rowsJ2 88 89 17 19 ≤ 5159156157 := by decide +kernel

theorem rows22250R_2259 : rowsJ2 88 89 19 21 ≤ 2180901657 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2244
#print axioms SieveCert.rows22250R_2259
