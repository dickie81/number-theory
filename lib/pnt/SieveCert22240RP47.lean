/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 477–482 of 5066

File 47 of 387: the parts `rows22240R_477` … `rows22240R_482` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 93612 in units of a depth-4 test: row 47 columns 34–34, row 47 columns
35–35, row 47 columns 36–36, row 47 columns 37–37, row 47 columns 38–38, row 47 columns 39–39), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_477 : rowsJ2 47 48 34 35 ≤ 167984869823 := by decide +kernel

theorem rows22240R_478 : rowsJ2 47 48 35 36 ≤ 141775572115 := by decide +kernel

theorem rows22240R_479 : rowsJ2 47 48 36 37 ≤ 115169751425 := by decide +kernel

theorem rows22240R_480 : rowsJ2 47 48 37 38 ≤ 93461810211 := by decide +kernel

theorem rows22240R_481 : rowsJ2 47 48 38 39 ≤ 71909230020 := by decide +kernel

theorem rows22240R_482 : rowsJ2 47 48 39 40 ≤ 55254984596 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_477
#print axioms SieveCert.rows22240R_482
