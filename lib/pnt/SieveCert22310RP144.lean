/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 570–573 of 1732

File 144 of 430: the parts `rows22310R_570` … `rows22310R_573` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25024 tests: row 109 columns 96–97, row 109 columns 98–99, row 109 columns
100–101, row 109 columns 102–103), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_570 : rowsJ2 109 110 96 98 ≤ 3585462379368 := by decide +kernel

theorem rows22310R_571 : rowsJ2 109 110 98 100 ≤ 3175328868358 := by decide +kernel

theorem rows22310R_572 : rowsJ2 109 110 100 102 ≤ 2786358353663 := by decide +kernel

theorem rows22310R_573 : rowsJ2 109 110 102 104 ≤ 2554024498289 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_570
#print axioms SieveCert.rows22310R_573
