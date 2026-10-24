/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 44–47 of 561

File 11 of 142: the parts `rows22325R_44` … `rows22325R_47` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 27405 tests: row 48 columns 44–299, row 49 columns 0–34, row 49 columns
35–43, row 49 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_44 : rowsJ2 48 49 44 300 ≤ 372487299461680 := by decide +kernel

theorem rows22325R_45 : rowsJ2 49 50 0 35 ≤ 1669957050110692 := by decide +kernel

theorem rows22325R_46 : rowsJ2 49 50 35 44 ≤ 359890281601229 := by decide +kernel

theorem rows22325R_47 : rowsJ2 49 50 44 300 ≤ 459652365523320 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_44
#print axioms SieveCert.rows22325R_47
