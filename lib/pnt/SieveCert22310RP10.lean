/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 40–43 of 1732

File 10 of 430: the parts `rows22310R_40` … `rows22310R_43` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27010 tests: row 47 columns 35–43, row 47 columns 44–399, row 48 columns
0–34, row 48 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_40 : rowsJ2 47 48 35 44 ≤ 712321189972629 := by decide +kernel

theorem rows22310R_41 : rowsJ2 47 48 44 400 ≤ 256947413825126 := by decide +kernel

theorem rows22310R_42 : rowsJ2 48 49 0 35 ≤ 1361643122163707 := by decide +kernel

theorem rows22310R_43 : rowsJ2 48 49 35 44 ≤ 690831087741645 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_40
#print axioms SieveCert.rows22310R_43
