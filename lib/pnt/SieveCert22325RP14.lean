/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 55–58 of 561

File 14 of 142: the parts `rows22325R_55` … `rows22325R_58` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 23932 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns 44–51,
row 52 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_55 : rowsJ2 52 53 0 35 ≤ 1449771617343662 := by decide +kernel

theorem rows22325R_56 : rowsJ2 52 53 35 44 ≤ 364942132289872 := by decide +kernel

theorem rows22325R_57 : rowsJ2 52 53 44 52 ≤ 604943260718753 := by decide +kernel

theorem rows22325R_58 : rowsJ2 52 53 52 300 ≤ 69273349258065 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_55
#print axioms SieveCert.rows22325R_58
