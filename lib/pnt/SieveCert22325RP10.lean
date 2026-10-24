/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 40–43 of 561

File 10 of 142: the parts `rows22325R_40` … `rows22325R_43` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27010 tests: row 47 columns 35–43, row 47 columns 44–299, row 48 columns
0–34, row 48 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_40 : rowsJ2 47 48 35 44 ≤ 370387023399599 := by decide +kernel

theorem rows22325R_41 : rowsJ2 47 48 44 300 ≤ 279510498857610 := by decide +kernel

theorem rows22325R_42 : rowsJ2 48 49 0 35 ≤ 1746139396745109 := by decide +kernel

theorem rows22325R_43 : rowsJ2 48 49 35 44 ≤ 363638293311220 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_40
#print axioms SieveCert.rows22325R_43
