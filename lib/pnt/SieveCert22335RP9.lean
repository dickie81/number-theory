/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 36–39 of 549

File 9 of 140: the parts `rows22335R_36` … `rows22335R_39` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26194 tests: row 46 columns 0–34, row 46 columns 35–43, row 46 columns
44–299, row 47 columns 0–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_36 : rowsJ2 46 47 0 35 ≤ 1898659062554175 := by decide +kernel

theorem rows22335R_37 : rowsJ2 46 47 35 44 ≤ 379202044660841 := by decide +kernel

theorem rows22335R_38 : rowsJ2 46 47 44 300 ≤ 194286284534272 := by decide +kernel

theorem rows22335R_39 : rowsJ2 47 48 0 35 ≤ 1820700435479805 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_36
#print axioms SieveCert.rows22335R_39
