/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 671–674 of 1732

File 169 of 430: the parts `rows22310R_671` … `rows22310R_674` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26881 tests: row 115 columns 79–82, row 115 columns 83–85, row 115 columns
86–88, row 115 columns 89–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_671 : rowsJ2 115 116 79 83 ≤ 105478538343 := by decide +kernel

theorem rows22310R_672 : rowsJ2 115 116 83 86 ≤ 30300003306 := by decide +kernel

theorem rows22310R_673 : rowsJ2 115 116 86 89 ≤ 593263019973 := by decide +kernel

theorem rows22310R_674 : rowsJ2 115 116 89 91 ≤ 1144914718201 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_671
#print axioms SieveCert.rows22310R_674
