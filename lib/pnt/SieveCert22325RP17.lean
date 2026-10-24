/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 67–70 of 561

File 17 of 142: the parts `rows22325R_67` … `rows22325R_70` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24850 tests: row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–52,
row 55 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_67 : rowsJ2 55 56 0 35 ≤ 1243580634723868 := by decide +kernel

theorem rows22325R_68 : rowsJ2 55 56 35 44 ≤ 396303178199937 := by decide +kernel

theorem rows22325R_69 : rowsJ2 55 56 44 53 ≤ 641583006804157 := by decide +kernel

theorem rows22325R_70 : rowsJ2 55 56 53 300 ≤ 177523557907912 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_67
#print axioms SieveCert.rows22325R_70
