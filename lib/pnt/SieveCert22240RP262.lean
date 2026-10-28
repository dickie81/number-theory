/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3208–3223 of 5066

File 262 of 387: the parts `rows22240R_3208` … `rows22240R_3223` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99822 in units of a depth-4 test: row 111 columns 61–65, row 111
columns 66–70, row 111 columns 71–74, row 111 columns 75–77, row 111 columns 78–79, row 111 columns 80–82, row 111
columns 83–85, row 111 columns 86–87, row 111 columns 88–89, row 111 columns 90–91, row 111 columns 92–93, row 111
columns 94–94, row 111 columns 95–95, row 111 columns 96–96, row 111 columns 97–97, row 111 columns 98–98), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_3208 : rowsJ2 111 112 61 66 ≤ 3054062738902 := by decide +kernel

theorem rows22240R_3209 : rowsJ2 111 112 66 71 ≤ 732977192619 := by decide +kernel

theorem rows22240R_3210 : rowsJ2 111 112 71 75 ≤ 0 := by decide +kernel

theorem rows22240R_3211 : rowsJ2 111 112 75 78 ≤ 209203516301 := by decide +kernel

theorem rows22240R_3212 : rowsJ2 111 112 78 80 ≤ 369136786418 := by decide +kernel

theorem rows22240R_3213 : rowsJ2 111 112 80 83 ≤ 623820264678 := by decide +kernel

theorem rows22240R_3214 : rowsJ2 111 112 83 86 ≤ 2602363161459 := by decide +kernel

theorem rows22240R_3215 : rowsJ2 111 112 86 88 ≤ 3921174006198 := by decide +kernel

theorem rows22240R_3216 : rowsJ2 111 112 88 90 ≤ 6418583228993 := by decide +kernel

theorem rows22240R_3217 : rowsJ2 111 112 90 92 ≤ 9577720015232 := by decide +kernel

theorem rows22240R_3218 : rowsJ2 111 112 92 94 ≤ 13436950786170 := by decide +kernel

theorem rows22240R_3219 : rowsJ2 111 112 94 95 ≤ 8403044468989 := by decide +kernel

theorem rows22240R_3220 : rowsJ2 111 112 95 96 ≤ 9637517498738 := by decide +kernel

theorem rows22240R_3221 : rowsJ2 111 112 96 97 ≤ 10999816207571 := by decide +kernel

theorem rows22240R_3222 : rowsJ2 111 112 97 98 ≤ 12439726961615 := by decide +kernel

theorem rows22240R_3223 : rowsJ2 111 112 98 99 ≤ 14015750602998 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3208
#print axioms SieveCert.rows22240R_3223
