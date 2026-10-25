/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 161–164 of 1732

File 40 of 430: the parts `rows22310R_161` … `rows22310R_164` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27244 tests: row 69 columns 55–58, row 69 columns 59–62, row 69 columns
63–66, row 69 columns 67–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_161 : rowsJ2 69 70 55 59 ≤ 116653025904305 := by decide +kernel

theorem rows22310R_162 : rowsJ2 69 70 59 63 ≤ 160474700337267 := by decide +kernel

theorem rows22310R_163 : rowsJ2 69 70 63 67 ≤ 177619171125764 := by decide +kernel

theorem rows22310R_164 : rowsJ2 69 70 67 400 ≤ 124477787598956 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_161
#print axioms SieveCert.rows22310R_164
