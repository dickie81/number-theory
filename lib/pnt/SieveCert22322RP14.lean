/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 55–58 of 561

File 14 of 143: the parts `rows22322R_55` … `rows22322R_58` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23932 tests: row 52 columns 0–34, row 52 columns 35–43, row 52 columns 44–51,
row 52 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_55 : rowsJ2 52 53 0 35 ≤ 1516696150053241 := by decide +kernel

theorem rows22322R_56 : rowsJ2 52 53 35 44 ≤ 381401859834651 := by decide +kernel

theorem rows22322R_57 : rowsJ2 52 53 44 52 ≤ 608027785068461 := by decide +kernel

theorem rows22322R_58 : rowsJ2 52 53 52 300 ≤ 69517927165761 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_55
#print axioms SieveCert.rows22322R_58
