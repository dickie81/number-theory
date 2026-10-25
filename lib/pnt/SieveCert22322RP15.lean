/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 59–62 of 561

File 15 of 143: the parts `rows22322R_59` … `rows22322R_62` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24372 tests: row 53 columns 0–34, row 53 columns 35–43, row 53 columns 44–51,
row 53 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_59 : rowsJ2 53 54 0 35 ≤ 1445738624614240 := by decide +kernel

theorem rows22322R_60 : rowsJ2 53 54 35 44 ≤ 386975157171736 := by decide +kernel

theorem rows22322R_61 : rowsJ2 53 54 44 52 ≤ 601758766277980 := by decide +kernel

theorem rows22322R_62 : rowsJ2 53 54 52 300 ≤ 133037326849703 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_59
#print axioms SieveCert.rows22322R_62
