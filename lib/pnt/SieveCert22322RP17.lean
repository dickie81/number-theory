/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 67–70 of 561

File 17 of 143: the parts `rows22322R_67` … `rows22322R_70` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24850 tests: row 55 columns 0–34, row 55 columns 35–43, row 55 columns 44–52,
row 55 columns 53–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_67 : rowsJ2 55 56 0 35 ≤ 1308677986268323 := by decide +kernel

theorem rows22322R_68 : rowsJ2 55 56 35 44 ≤ 406934395856363 := by decide +kernel

theorem rows22322R_69 : rowsJ2 55 56 44 53 ≤ 643842679268077 := by decide +kernel

theorem rows22322R_70 : rowsJ2 55 56 53 300 ≤ 178160662574201 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_67
#print axioms SieveCert.rows22322R_70
