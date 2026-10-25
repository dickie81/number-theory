/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 552–555 of 561

File 141 of 143: the parts `rows22322R_552` … `rows22322R_555` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27058 tests: rows 221–223, rows 224–226, rows 227–229, rows 230–233), each a
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

theorem rows22322R_552 : rows2 221 224 ≤ 30852765619901798 := by decide +kernel

theorem rows22322R_553 : rows2 224 227 ≤ 30935408198339509 := by decide +kernel

theorem rows22322R_554 : rows2 227 230 ≤ 31373900152686889 := by decide +kernel

theorem rows22322R_555 : rows2 230 234 ≤ 42088002826068876 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_552
#print axioms SieveCert.rows22322R_555
