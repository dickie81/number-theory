/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1367–1370 of 1732

File 343 of 430: the parts `rows22310R_1367` … `rows22310R_1370` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28773 tests: row 163 columns 56–61, row 163 columns 62–65, row 163 columns
66–68, row 163 columns 69–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1367 : rowsJ2 163 164 56 62 ≤ 22086153180474 := by decide +kernel

theorem rows22310R_1368 : rowsJ2 163 164 62 66 ≤ 24856180459640 := by decide +kernel

theorem rows22310R_1369 : rowsJ2 163 164 66 69 ≤ 23754783602278 := by decide +kernel

theorem rows22310R_1370 : rowsJ2 163 164 69 73 ≤ 25511932422939 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1367
#print axioms SieveCert.rows22310R_1370
