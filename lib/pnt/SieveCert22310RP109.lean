/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 433–436 of 1732

File 109 of 430: the parts `rows22310R_433` … `rows22310R_436` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29250 tests: row 100 columns 51–59, row 100 columns 60–78, row 100 columns
79–85, row 100 columns 86–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_433 : rowsJ2 100 101 51 60 ≤ 243075632637713 := by decide +kernel

theorem rows22310R_434 : rowsJ2 100 101 60 79 ≤ 285039151891343 := by decide +kernel

theorem rows22310R_435 : rowsJ2 100 101 79 86 ≤ 39210492603632 := by decide +kernel

theorem rows22310R_436 : rowsJ2 100 101 86 90 ≤ 11283475819166 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_433
#print axioms SieveCert.rows22310R_436
