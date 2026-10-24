/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 36–39 of 561

File 9 of 142: the parts `rows22325R_36` … `rows22325R_39` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 26194 tests: row 46 columns 0–34, row 46 columns 35–43, row 46 columns
44–299, row 47 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22325R_36 : rowsJ2 46 47 0 35 ≤ 1901110264041098 := by decide +kernel

theorem rows22325R_37 : rowsJ2 46 47 35 44 ≤ 379623235057181 := by decide +kernel

theorem rows22325R_38 : rowsJ2 46 47 44 300 ≤ 194479689966536 := by decide +kernel

theorem rows22325R_39 : rowsJ2 47 48 0 35 ≤ 1823052169700708 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_36
#print axioms SieveCert.rows22325R_39
