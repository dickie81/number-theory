/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2283–2296 of 5066

File 198 of 387: the parts `rows22240R_2283` … `rows22240R_2296` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 98113 in units of a depth-4 test: row 89 columns 59–60, row 89 columns
61–62, row 89 columns 63–64, row 89 columns 65–67, row 89 columns 68–71, row 89 columns 72–75, row 89 columns 76–78,
row 89 columns 79–79, row 89 columns 80–80, row 89 columns 81–81, row 89 columns 82–82, row 89 columns 83–83, row 89
columns 84–84, row 89 columns 85–85), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_2283 : rowsJ2 89 90 59 61 ≤ 0 := by decide +kernel

theorem rows22240R_2284 : rowsJ2 89 90 61 63 ≤ 0 := by decide +kernel

theorem rows22240R_2285 : rowsJ2 89 90 63 65 ≤ 0 := by decide +kernel

theorem rows22240R_2286 : rowsJ2 89 90 65 68 ≤ 0 := by decide +kernel

theorem rows22240R_2287 : rowsJ2 89 90 68 72 ≤ 0 := by decide +kernel

theorem rows22240R_2288 : rowsJ2 89 90 72 76 ≤ 0 := by decide +kernel

theorem rows22240R_2289 : rowsJ2 89 90 76 79 ≤ 654848853420 := by decide +kernel

theorem rows22240R_2290 : rowsJ2 89 90 79 80 ≤ 667364010594 := by decide +kernel

theorem rows22240R_2291 : rowsJ2 89 90 80 81 ≤ 1014089990038 := by decide +kernel

theorem rows22240R_2292 : rowsJ2 89 90 81 82 ≤ 1488194274363 := by decide +kernel

theorem rows22240R_2293 : rowsJ2 89 90 82 83 ≤ 2113594260570 := by decide +kernel

theorem rows22240R_2294 : rowsJ2 89 90 83 84 ≤ 2881950807117 := by decide +kernel

theorem rows22240R_2295 : rowsJ2 89 90 84 85 ≤ 3819942507313 := by decide +kernel

theorem rows22240R_2296 : rowsJ2 89 90 85 86 ≤ 4921621697855 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2283
#print axioms SieveCert.rows22240R_2296
