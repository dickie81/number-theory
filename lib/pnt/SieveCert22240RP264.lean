/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3238–3253 of 5066

File 264 of 387: the parts `rows22240R_3238` … `rows22240R_3253` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94902 in units of a depth-4 test: row 112 columns 69–72, row 112
columns 73–75, row 112 columns 76–78, row 112 columns 79–81, row 112 columns 82–84, row 112 columns 85–86, row 112
columns 87–88, row 112 columns 89–90, row 112 columns 91–92, row 112 columns 93–93, row 112 columns 94–94, row 112
columns 95–95, row 112 columns 96–96, row 112 columns 97–97, row 112 columns 98–339, row 113 columns 0–25), each a
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

theorem rows22240R_3238 : rowsJ2 112 113 69 73 ≤ 0 := by decide +kernel

theorem rows22240R_3239 : rowsJ2 112 113 73 76 ≤ 0 := by decide +kernel

theorem rows22240R_3240 : rowsJ2 112 113 76 79 ≤ 325206468331 := by decide +kernel

theorem rows22240R_3241 : rowsJ2 112 113 79 82 ≤ 298671130634 := by decide +kernel

theorem rows22240R_3242 : rowsJ2 112 113 82 85 ≤ 1893149859330 := by decide +kernel

theorem rows22240R_3243 : rowsJ2 112 113 85 87 ≤ 3242157059320 := by decide +kernel

theorem rows22240R_3244 : rowsJ2 112 113 87 89 ≤ 5559461950117 := by decide +kernel

theorem rows22240R_3245 : rowsJ2 112 113 89 91 ≤ 8537565268765 := by decide +kernel

theorem rows22240R_3246 : rowsJ2 112 113 91 93 ≤ 12214107277478 := by decide +kernel

theorem rows22240R_3247 : rowsJ2 112 113 93 94 ≤ 7722396009265 := by decide +kernel

theorem rows22240R_3248 : rowsJ2 112 113 94 95 ≤ 8910219677724 := by decide +kernel

theorem rows22240R_3249 : rowsJ2 112 113 95 96 ≤ 10225462137149 := by decide +kernel

theorem rows22240R_3250 : rowsJ2 112 113 96 97 ≤ 11617816726398 := by decide +kernel

theorem rows22240R_3251 : rowsJ2 112 113 97 98 ≤ 13145766481107 := by decide +kernel

theorem rows22240R_3252 : rowsJ2 112 113 98 340 ≤ 1463512995011523 := by decide +kernel

theorem rows22240R_3253 : rowsJ2 113 114 0 26 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3238
#print axioms SieveCert.rows22240R_3253
