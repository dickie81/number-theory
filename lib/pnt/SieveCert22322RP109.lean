/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 418–421 of 561

File 109 of 143: the parts `rows22322R_418` … `rows22322R_421` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 29864 tests: row 118 columns 0–48, row 118 columns 49–54, row 118 columns
55–61, row 118 columns 62–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_418 : rowsJ2 118 119 0 49 ≤ 214457726686025 := by decide +kernel

theorem rows22322R_419 : rowsJ2 118 119 49 55 ≤ 70014009531641 := by decide +kernel

theorem rows22322R_420 : rowsJ2 118 119 55 62 ≤ 42175049262250 := by decide +kernel

theorem rows22322R_421 : rowsJ2 118 119 62 72 ≤ 8676381166093 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_418
#print axioms SieveCert.rows22322R_421
