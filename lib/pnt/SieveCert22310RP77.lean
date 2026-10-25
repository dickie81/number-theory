/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 309–312 of 1732

File 77 of 430: the parts `rows22310R_309` … `rows22310R_312` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27414 tests: row 86 columns 67–77, row 86 columns 78–399, row 87 columns
0–34, row 87 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_309 : rowsJ2 86 87 67 78 ≤ 261473624642275 := by decide +kernel

theorem rows22310R_310 : rowsJ2 86 87 78 400 ≤ 139487833897658 := by decide +kernel

theorem rows22310R_311 : rowsJ2 87 88 0 35 ≤ 534415115426767 := by decide +kernel

theorem rows22310R_312 : rowsJ2 87 88 35 44 ≤ 61324959250597 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_309
#print axioms SieveCert.rows22310R_312
