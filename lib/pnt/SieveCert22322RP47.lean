/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 179–182 of 561

File 47 of 143: the parts `rows22322R_179` … `rows22322R_182` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 24495 tests: row 80 columns 80–299, row 81 columns 0–35, row 81 columns
36–61, row 81 columns 62–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_179 : rowsJ2 80 81 80 300 ≤ 3123180953462 := by decide +kernel

theorem rows22322R_180 : rowsJ2 81 82 0 36 ≤ 577570808351921 := by decide +kernel

theorem rows22322R_181 : rowsJ2 81 82 36 62 ≤ 526252398259551 := by decide +kernel

theorem rows22322R_182 : rowsJ2 81 82 62 68 ≤ 3318912129585 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_179
#print axioms SieveCert.rows22322R_182
