/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1421–1423 of 1732

File 357 of 430: the parts `rows22310R_1421` … `rows22310R_1423` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22359 tests: row 169 columns 64–67, row 169 columns 68–71, row 169 columns
72–76), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1421 : rowsJ2 169 170 64 68 ≤ 33412963148245 := by decide +kernel

theorem rows22310R_1422 : rowsJ2 169 170 68 72 ≤ 22757900376697 := by decide +kernel

theorem rows22310R_1423 : rowsJ2 169 170 72 77 ≤ 16163276662754 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1421
#print axioms SieveCert.rows22310R_1423
