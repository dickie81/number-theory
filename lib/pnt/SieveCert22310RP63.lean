/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 253–256 of 1732

File 63 of 430: the parts `rows22310R_253` … `rows22310R_256` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29260 tests: row 80 columns 0–34, row 80 columns 35–43, row 80 columns 44–49,
row 80 columns 50–54), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_253 : rowsJ2 80 81 0 35 ≤ 713481527680541 := by decide +kernel

theorem rows22310R_254 : rowsJ2 80 81 35 44 ≤ 103509029982628 := by decide +kernel

theorem rows22310R_255 : rowsJ2 80 81 44 50 ≤ 81308097135122 := by decide +kernel

theorem rows22310R_256 : rowsJ2 80 81 50 55 ≤ 126092351232150 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_253
#print axioms SieveCert.rows22310R_256
