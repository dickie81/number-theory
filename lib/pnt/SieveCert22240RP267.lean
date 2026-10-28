/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3284–3297 of 5066

File 267 of 387: the parts `rows22240R_3284` … `rows22240R_3297` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 99258 in units of a depth-4 test: row 114 columns 35–36, row 114
columns 37–38, row 114 columns 39–41, row 114 columns 42–45, row 114 columns 46–54, row 114 columns 55–61, row 114
columns 62–64, row 114 columns 65–67, row 114 columns 68–70, row 114 columns 71–74, row 114 columns 75–77, row 114
columns 78–80, row 114 columns 81–83, row 114 columns 84–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3284 : rowsJ2 114 115 35 37 ≤ 22155415325407 := by decide +kernel

theorem rows22240R_3285 : rowsJ2 114 115 37 39 ≤ 17249871762581 := by decide +kernel

theorem rows22240R_3286 : rowsJ2 114 115 39 42 ≤ 14714267766066 := by decide +kernel

theorem rows22240R_3287 : rowsJ2 114 115 42 46 ≤ 7019183004015 := by decide +kernel

theorem rows22240R_3288 : rowsJ2 114 115 46 55 ≤ 540928524503 := by decide +kernel

theorem rows22240R_3289 : rowsJ2 114 115 55 62 ≤ 2399882631346 := by decide +kernel

theorem rows22240R_3290 : rowsJ2 114 115 62 65 ≤ 3712566480010 := by decide +kernel

theorem rows22240R_3291 : rowsJ2 114 115 65 68 ≤ 3796473574801 := by decide +kernel

theorem rows22240R_3292 : rowsJ2 114 115 68 71 ≤ 2112572401282 := by decide +kernel

theorem rows22240R_3293 : rowsJ2 114 115 71 75 ≤ 0 := by decide +kernel

theorem rows22240R_3294 : rowsJ2 114 115 75 78 ≤ 76744299288 := by decide +kernel

theorem rows22240R_3295 : rowsJ2 114 115 78 81 ≤ 13032857116 := by decide +kernel

theorem rows22240R_3296 : rowsJ2 114 115 81 84 ≤ 1398828953836 := by decide +kernel

theorem rows22240R_3297 : rowsJ2 114 115 84 87 ≤ 5064457450991 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3284
#print axioms SieveCert.rows22240R_3297
