/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 114–117 of 561

File 30 of 143: the parts `rows22322R_114` … `rows22322R_117` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24617 tests: row 68 columns 0–34, row 68 columns 35–47, row 68 columns 48–67,
row 68 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_114 : rowsJ2 68 69 0 35 ≤ 663451650730604 := by decide +kernel

theorem rows22322R_115 : rowsJ2 68 69 35 48 ≤ 738436252467454 := by decide +kernel

theorem rows22322R_116 : rowsJ2 68 69 48 68 ≤ 530200812033332 := by decide +kernel

theorem rows22322R_117 : rowsJ2 68 69 68 300 ≤ 10338087066882 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_114
#print axioms SieveCert.rows22322R_117
