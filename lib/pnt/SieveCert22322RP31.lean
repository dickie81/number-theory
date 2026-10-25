/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 118–121 of 561

File 31 of 143: the parts `rows22322R_118` … `rows22322R_121` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 25639 tests: row 69 columns 0–34, row 69 columns 35–48, row 69 columns 49–67,
row 69 columns 68–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
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

theorem rows22322R_118 : rowsJ2 69 70 0 35 ≤ 637494206099126 := by decide +kernel

theorem rows22322R_119 : rowsJ2 69 70 35 49 ≤ 770477604593282 := by decide +kernel

theorem rows22322R_120 : rowsJ2 69 70 49 68 ≤ 450935482426845 := by decide +kernel

theorem rows22322R_121 : rowsJ2 69 70 68 300 ≤ 17207393540499 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_118
#print axioms SieveCert.rows22322R_121
