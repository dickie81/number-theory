/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 441–444 of 1732

File 111 of 430: the parts `rows22310R_441` … `rows22310R_444` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29742 tests: row 100 columns 99–399, row 101 columns 0–34, row 101 columns
35–43, row 101 columns 44–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_441 : rowsJ2 100 101 99 400 ≤ 8325404510445 := by decide +kernel

theorem rows22310R_442 : rowsJ2 101 102 0 35 ≤ 226994214105638 := by decide +kernel

theorem rows22310R_443 : rowsJ2 101 102 35 44 ≤ 105292957261463 := by decide +kernel

theorem rows22310R_444 : rowsJ2 101 102 44 51 ≤ 215935320430216 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_441
#print axioms SieveCert.rows22310R_444
