/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 197–200 of 1732

File 49 of 430: the parts `rows22310R_197` … `rows22310R_200` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24840 tests: row 73 columns 67–71, row 73 columns 72–399, row 74 columns
0–34, row 74 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_197 : rowsJ2 73 74 67 72 ≤ 187247278072491 := by decide +kernel

theorem rows22310R_198 : rowsJ2 73 74 72 400 ≤ 69072534404095 := by decide +kernel

theorem rows22310R_199 : rowsJ2 74 75 0 35 ≤ 864378809098563 := by decide +kernel

theorem rows22310R_200 : rowsJ2 74 75 35 44 ≤ 170623620326008 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_197
#print axioms SieveCert.rows22310R_200
