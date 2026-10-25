/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 537–540 of 561

File 137 of 143: the parts `rows22322R_537` … `rows22322R_540` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29064 tests: rows 174–176, rows 177–179, rows 180–183, rows 184–187), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_537 : rows2 174 177 ≤ 18225229139988974 := by decide +kernel

theorem rows22322R_538 : rows2 177 180 ≤ 19591640104249381 := by decide +kernel

theorem rows22322R_539 : rows2 180 184 ≤ 28316076824449675 := by decide +kernel

theorem rows22322R_540 : rows2 184 188 ≤ 30471911516321387 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_537
#print axioms SieveCert.rows22322R_540
