/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1440–1443 of 1732

File 362 of 430: the parts `rows22310R_1440` … `rows22310R_1443` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 25786 tests: row 171 columns 76–81, row 171 columns 82–399, row 172 columns
0–52, row 172 columns 53–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_1440 : rowsJ2 171 172 76 82 ≤ 7474103406088 := by decide +kernel

theorem rows22310R_1441 : rowsJ2 171 172 82 400 ≤ 1385913938070187 := by decide +kernel

theorem rows22310R_1442 : rowsJ2 172 173 0 53 ≤ 61188773197850 := by decide +kernel

theorem rows22310R_1443 : rowsJ2 172 173 53 59 ≤ 29822440864224 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1440
#print axioms SieveCert.rows22310R_1443
