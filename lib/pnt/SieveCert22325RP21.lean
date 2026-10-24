/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 83–86 of 561

File 21 of 142: the parts `rows22325R_83` … `rows22325R_86` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24509 tests: row 59 columns 0–34, row 59 columns 35–43, row 59 columns 44–55,
row 59 columns 56–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22325R_83 : rowsJ2 59 60 0 35 ≤ 998037757746809 := by decide +kernel

theorem rows22325R_84 : rowsJ2 59 60 35 44 ≤ 463587023342014 := by decide +kernel

theorem rows22325R_85 : rowsJ2 59 60 44 56 ≤ 723002238644727 := by decide +kernel

theorem rows22325R_86 : rowsJ2 59 60 56 300 ≤ 173610634313147 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_83
#print axioms SieveCert.rows22325R_86
