/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 874–877 of 1732

File 219 of 430: the parts `rows22310R_874` … `rows22310R_877` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29199 tests: row 126 columns 35–66, row 126 columns 67–74, row 126 columns
75–78, row 126 columns 79–81), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_874 : rowsJ2 126 127 35 67 ≤ 338231961538865 := by decide +kernel

theorem rows22310R_875 : rowsJ2 126 127 67 75 ≤ 478980588737 := by decide +kernel

theorem rows22310R_876 : rowsJ2 126 127 75 79 ≤ 0 := by decide +kernel

theorem rows22310R_877 : rowsJ2 126 127 79 82 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_874
#print axioms SieveCert.rows22310R_877
