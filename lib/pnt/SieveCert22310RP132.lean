/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 522–526 of 1732

File 132 of 430: the parts `rows22310R_522` … `rows22310R_526` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 28359 tests: row 106 columns 98–99, row 106 columns 100–101, row 106 columns
102–103, row 106 columns 104–105, row 106 columns 106–399), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_522 : rowsJ2 106 107 98 100 ≤ 4679502372992 := by decide +kernel

theorem rows22310R_523 : rowsJ2 106 107 100 102 ≤ 4210926618684 := by decide +kernel

theorem rows22310R_524 : rowsJ2 106 107 102 104 ≤ 3781912495280 := by decide +kernel

theorem rows22310R_525 : rowsJ2 106 107 104 106 ≤ 3581655992595 := by decide +kernel

theorem rows22310R_526 : rowsJ2 106 107 106 400 ≤ 1798832045516 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_522
#print axioms SieveCert.rows22310R_526
