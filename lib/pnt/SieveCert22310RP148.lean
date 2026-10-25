/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 586–589 of 1732

File 148 of 430: the parts `rows22310R_586` … `rows22310R_589` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25392 tests: row 110 columns 94–95, row 110 columns 96–97, row 110 columns
98–99, row 110 columns 100–101), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_586 : rowsJ2 110 111 94 96 ≤ 3529708274829 := by decide +kernel

theorem rows22310R_587 : rowsJ2 110 111 96 98 ≤ 3124957174912 := by decide +kernel

theorem rows22310R_588 : rowsJ2 110 111 98 100 ≤ 2741704522185 := by decide +kernel

theorem rows22310R_589 : rowsJ2 110 111 100 102 ≤ 2397934911805 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_586
#print axioms SieveCert.rows22310R_589
