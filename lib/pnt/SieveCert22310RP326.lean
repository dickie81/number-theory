/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1300–1302 of 1732

File 326 of 430: the parts `rows22310R_1300` … `rows22310R_1302` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22425 tests: row 156 columns 77–80, row 156 columns 81–84, row 156 columns
85–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1300 : rowsJ2 156 157 77 81 ≤ 12491374677274 := by decide +kernel

theorem rows22310R_1301 : rowsJ2 156 157 81 85 ≤ 7111069525009 := by decide +kernel

theorem rows22310R_1302 : rowsJ2 156 157 85 90 ≤ 3681754512051 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1300
#print axioms SieveCert.rows22310R_1302
