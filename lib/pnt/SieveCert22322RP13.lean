/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 51–54 of 561

File 13 of 143: the parts `rows22322R_51` … `rows22322R_54` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 23379 tests: row 51 columns 0–34, row 51 columns 35–43, row 51 columns 44–50,
row 51 columns 51–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_51 : rowsJ2 51 52 0 35 ≤ 1589221103174545 := by decide +kernel

theorem rows22322R_52 : rowsJ2 51 52 35 44 ≤ 378523703420167 := by decide +kernel

theorem rows22322R_53 : rowsJ2 51 52 44 51 ≤ 541484284933034 := by decide +kernel

theorem rows22322R_54 : rowsJ2 51 52 51 300 ≤ 73445406559828 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_51
#print axioms SieveCert.rows22322R_54
