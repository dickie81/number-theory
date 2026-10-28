/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3330–3344 of 5066

File 270 of 387: the parts `rows22240R_3330` … `rows22240R_3344` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99065 in units of a depth-4 test: row 115 columns 95–95, row 115
columns 96–96, row 115 columns 97–339, row 116 columns 0–26, row 116 columns 27–30, row 116 columns 31–32, row 116
columns 33–34, row 116 columns 35–36, row 116 columns 37–39, row 116 columns 40–43, row 116 columns 44–52, row 116
columns 53–60, row 116 columns 61–63, row 116 columns 64–65, row 116 columns 66–67), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3330 : rowsJ2 115 116 95 96 ≤ 12022515703743 := by decide +kernel

theorem rows22240R_3331 : rowsJ2 115 116 96 97 ≤ 13629341829351 := by decide +kernel

theorem rows22240R_3332 : rowsJ2 115 116 97 340 ≤ 1564772051037401 := by decide +kernel

theorem rows22240R_3333 : rowsJ2 116 117 0 27 ≤ 1060297628540 := by decide +kernel

theorem rows22240R_3334 : rowsJ2 116 117 27 31 ≤ 12912829629844 := by decide +kernel

theorem rows22240R_3335 : rowsJ2 116 117 31 33 ≤ 16454204521136 := by decide +kernel

theorem rows22240R_3336 : rowsJ2 116 117 33 35 ≤ 22429297337570 := by decide +kernel

theorem rows22240R_3337 : rowsJ2 116 117 35 37 ≤ 18069261577465 := by decide +kernel

theorem rows22240R_3338 : rowsJ2 116 117 37 40 ≤ 18025833867675 := by decide +kernel

theorem rows22240R_3339 : rowsJ2 116 117 40 44 ≤ 8495940442815 := by decide +kernel

theorem rows22240R_3340 : rowsJ2 116 117 44 53 ≤ 1114782649708 := by decide +kernel

theorem rows22240R_3341 : rowsJ2 116 117 53 61 ≤ 2486135084235 := by decide +kernel

theorem rows22240R_3342 : rowsJ2 116 117 61 64 ≤ 4515868403804 := by decide +kernel

theorem rows22240R_3343 : rowsJ2 116 117 64 66 ≤ 3752394125381 := by decide +kernel

theorem rows22240R_3344 : rowsJ2 116 117 66 68 ≤ 3752575158145 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3330
#print axioms SieveCert.rows22240R_3344
