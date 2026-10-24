/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 31–35 of 561

File 8 of 142: the parts `rows22325R_31` … `rows22325R_35` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 25741 tests: row 44 columns 35–43, row 44 columns 44–299, row 45 columns
0–34, row 45 columns 35–43, row 45 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_31 : rowsJ2 44 45 35 44 ≤ 406349349112437 := by decide +kernel

theorem rows22325R_32 : rowsJ2 44 45 44 300 ≤ 57428064780197 := by decide +kernel

theorem rows22325R_33 : rowsJ2 45 46 0 35 ≤ 1979919803976275 := by decide +kernel

theorem rows22325R_34 : rowsJ2 45 46 35 44 ≤ 391772921755339 := by decide +kernel

theorem rows22325R_35 : rowsJ2 45 46 44 300 ≤ 121269678329750 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_31
#print axioms SieveCert.rows22325R_35
