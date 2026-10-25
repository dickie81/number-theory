/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1371–1374 of 1732

File 344 of 430: the parts `rows22310R_1371` … `rows22310R_1374` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28706 tests: row 163 columns 73–76, row 163 columns 77–81, row 163 columns
82–86, row 163 columns 87–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1371 : rowsJ2 163 164 73 77 ≤ 16534312139201 := by decide +kernel

theorem rows22310R_1372 : rowsJ2 163 164 77 82 ≤ 10948549497513 := by decide +kernel

theorem rows22310R_1373 : rowsJ2 163 164 82 87 ≤ 3787498303130 := by decide +kernel

theorem rows22310R_1374 : rowsJ2 163 164 87 400 ≤ 606695652218326 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1371
#print axioms SieveCert.rows22310R_1374
