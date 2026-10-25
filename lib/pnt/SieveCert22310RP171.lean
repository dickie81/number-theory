/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 679–682 of 1732

File 171 of 430: the parts `rows22310R_679` … `rows22310R_682` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 26680 tests: row 115 columns 99–100, row 115 columns 101–102, row 115 columns
103–105, row 115 columns 106–108), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_679 : rowsJ2 115 116 99 101 ≤ 938963334879 := by decide +kernel

theorem rows22310R_680 : rowsJ2 115 116 101 103 ≤ 951845987132 := by decide +kernel

theorem rows22310R_681 : rowsJ2 115 116 103 106 ≤ 2153490964568 := by decide +kernel

theorem rows22310R_682 : rowsJ2 115 116 106 109 ≤ 3925105505391 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_679
#print axioms SieveCert.rows22310R_682
