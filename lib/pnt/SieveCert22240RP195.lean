/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2243–2254 of 5066

File 195 of 387: the parts `rows22240R_2243` … `rows22240R_2254` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 98144 in units of a depth-4 test: row 88 columns 69–72, row 88 columns
73–76, row 88 columns 77–78, row 88 columns 79–79, row 88 columns 80–80, row 88 columns 81–81, row 88 columns 82–82,
row 88 columns 83–83, row 88 columns 84–84, row 88 columns 85–85, row 88 columns 86–86, row 88 columns 87–87), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2243 : rowsJ2 88 89 69 73 ≤ 0 := by decide +kernel

theorem rows22240R_2244 : rowsJ2 88 89 73 77 ≤ 64853020423 := by decide +kernel

theorem rows22240R_2245 : rowsJ2 88 89 77 79 ≤ 841178780215 := by decide +kernel

theorem rows22240R_2246 : rowsJ2 88 89 79 80 ≤ 673496324679 := by decide +kernel

theorem rows22240R_2247 : rowsJ2 88 89 80 81 ≤ 1023411642775 := by decide +kernel

theorem rows22240R_2248 : rowsJ2 88 89 81 82 ≤ 1499446746254 := by decide +kernel

theorem rows22240R_2249 : rowsJ2 88 89 82 83 ≤ 2125274344305 := by decide +kernel

theorem rows22240R_2250 : rowsJ2 88 89 83 84 ≤ 2891937680179 := by decide +kernel

theorem rows22240R_2251 : rowsJ2 88 89 84 85 ≤ 3825759887129 := by decide +kernel

theorem rows22240R_2252 : rowsJ2 88 89 85 86 ≤ 4920193427448 := by decide +kernel

theorem rows22240R_2253 : rowsJ2 88 89 86 87 ≤ 6204744764848 := by decide +kernel

theorem rows22240R_2254 : rowsJ2 88 89 87 88 ≤ 7676056806313 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2243
#print axioms SieveCert.rows22240R_2254
