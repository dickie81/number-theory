/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 63–66 of 561

File 16 of 143: the parts `rows22322R_63` … `rows22322R_66` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24660 tests: row 54 columns 0–34, row 54 columns 35–43, row 54 columns 44–51,
row 54 columns 52–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_63 : rowsJ2 54 55 0 35 ≤ 1376253628449588 := by decide +kernel

theorem rows22322R_64 : rowsJ2 54 55 35 44 ≤ 395672004859393 := by decide +kernel

theorem rows22322R_65 : rowsJ2 54 55 44 52 ≤ 590914383069190 := by decide +kernel

theorem rows22322R_66 : rowsJ2 54 55 52 300 ≤ 190480155507156 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_63
#print axioms SieveCert.rows22322R_66
