/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1665–1667 of 1732

File 417 of 430: the parts `rows22310R_1665` … `rows22310R_1667` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22888 tests: rows 237–238, rows 239–240, rows 241–242), each a sum of refined
costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1665 : rows2 237 239 ≤ 9495326146886490 := by decide +kernel

theorem rows22310R_1666 : rows2 239 241 ≤ 9840591511023985 := by decide +kernel

theorem rows22310R_1667 : rows2 241 243 ≤ 10190557396391035 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1665
#print axioms SieveCert.rows22310R_1667
