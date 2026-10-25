/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 890–893 of 1732

File 223 of 430: the parts `rows22310R_890` … `rows22310R_893` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28680 tests: row 127 columns 0–34, row 127 columns 35–66, row 127 columns
67–73, row 127 columns 74–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_890 : rowsJ2 127 128 0 35 ≤ 133785722757498 := by decide +kernel

theorem rows22310R_891 : rowsJ2 127 128 35 67 ≤ 316425014788346 := by decide +kernel

theorem rows22310R_892 : rowsJ2 127 128 67 74 ≤ 305052061589 := by decide +kernel

theorem rows22310R_893 : rowsJ2 127 128 74 78 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_890
#print axioms SieveCert.rows22310R_893
