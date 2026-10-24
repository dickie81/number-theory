/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 83–86 of 549

File 21 of 140: the parts `rows22335R_83` … `rows22335R_86` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 24509 tests: row 59 columns 0–34, row 59 columns 35–43, row 59 columns 44–55,
row 59 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_83 : rowsJ2 59 60 0 35 ≤ 996749479619535 := by decide +kernel

theorem rows22335R_84 : rowsJ2 59 60 35 44 ≤ 463126516302224 := by decide +kernel

theorem rows22335R_85 : rowsJ2 59 60 44 56 ≤ 722263812951851 := by decide +kernel

theorem rows22335R_86 : rowsJ2 59 60 56 300 ≤ 173427259794256 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_83
#print axioms SieveCert.rows22335R_86
