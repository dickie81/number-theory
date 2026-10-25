/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 578–581 of 1732

File 146 of 430: the parts `rows22310R_578` … `rows22310R_581` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29230 tests: row 110 columns 35–43, row 110 columns 44–55, row 110 columns
56–77, row 110 columns 78–82), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_578 : rowsJ2 110 111 35 44 ≤ 184799108120092 := by decide +kernel

theorem rows22310R_579 : rowsJ2 110 111 44 56 ≤ 282520482217041 := by decide +kernel

theorem rows22310R_580 : rowsJ2 110 111 56 78 ≤ 212331679329010 := by decide +kernel

theorem rows22310R_581 : rowsJ2 110 111 78 83 ≤ 7113574049839 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_578
#print axioms SieveCert.rows22310R_581
