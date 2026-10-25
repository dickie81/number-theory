/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 189–192 of 1732

File 47 of 430: the parts `rows22310R_189` … `rows22310R_192` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23426 tests: row 72 columns 72–399, row 73 columns 0–34, row 73 columns
35–43, row 73 columns 44–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_189 : rowsJ2 72 73 72 400 ≤ 35782335727681 := by decide +kernel

theorem rows22310R_190 : rowsJ2 73 74 0 35 ≤ 888770809468763 := by decide +kernel

theorem rows22310R_191 : rowsJ2 73 74 35 44 ≤ 184305159525431 := by decide +kernel

theorem rows22310R_192 : rowsJ2 73 74 44 50 ≤ 92383139763812 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_189
#print axioms SieveCert.rows22310R_192
