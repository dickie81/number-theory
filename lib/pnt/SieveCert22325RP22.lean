/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 87–90 of 561

File 22 of 142: the parts `rows22325R_87` … `rows22325R_90` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24188 tests: row 60 columns 0–34, row 60 columns 35–43, row 60 columns 44–56,
row 60 columns 57–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_87 : rowsJ2 60 61 0 35 ≤ 943127830317434 := by decide +kernel

theorem rows22325R_88 : rowsJ2 60 61 35 44 ≤ 477632221690240 := by decide +kernel

theorem rows22325R_89 : rowsJ2 60 61 44 57 ≤ 743005629467896 := by decide +kernel

theorem rows22325R_90 : rowsJ2 60 61 57 300 ≤ 157253873832604 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_87
#print axioms SieveCert.rows22325R_90
