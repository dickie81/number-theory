/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 794–797 of 1732

File 199 of 430: the parts `rows22310R_794` … `rows22310R_797` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29256 tests: row 121 columns 97–99, row 121 columns 100–102, row 121 columns
103–105, row 121 columns 106–108), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_794 : rowsJ2 121 122 97 100 ≤ 145970641412 := by decide +kernel

theorem rows22310R_795 : rowsJ2 121 122 100 103 ≤ 474385128363 := by decide +kernel

theorem rows22310R_796 : rowsJ2 121 122 103 106 ≤ 2356768246761 := by decide +kernel

theorem rows22310R_797 : rowsJ2 121 122 106 109 ≤ 5289945428885 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_794
#print axioms SieveCert.rows22310R_797
