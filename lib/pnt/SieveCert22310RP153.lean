/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 606–609 of 1732

File 153 of 430: the parts `rows22310R_606` … `rows22310R_609` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23184 tests: row 111 columns 99–100, row 111 columns 101–102, row 111 columns
103–104, row 111 columns 105–106), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_606 : rowsJ2 111 112 99 101 ≤ 2169297217486 := by decide +kernel

theorem rows22310R_607 : rowsJ2 111 112 101 103 ≤ 1942888305370 := by decide +kernel

theorem rows22310R_608 : rowsJ2 111 112 103 105 ≤ 1979848293309 := by decide +kernel

theorem rows22310R_609 : rowsJ2 111 112 105 107 ≤ 2290944513260 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_606
#print axioms SieveCert.rows22310R_609
