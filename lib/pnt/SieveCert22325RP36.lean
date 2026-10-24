/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 136–139 of 561

File 36 of 142: the parts `rows22325R_136` … `rows22325R_139` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24137 tests: row 73 columns 58–67, row 73 columns 68–72, row 73 columns
73–299, row 74 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_136 : rowsJ2 73 74 58 68 ≤ 93915776119389 := by decide +kernel

theorem rows22325R_137 : rowsJ2 73 74 68 73 ≤ 22082536424883 := by decide +kernel

theorem rows22325R_138 : rowsJ2 73 74 73 300 ≤ 6935401391234 := by decide +kernel

theorem rows22325R_139 : rowsJ2 74 75 0 35 ≤ 532801126722948 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_136
#print axioms SieveCert.rows22325R_139
