/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 408–411 of 561

File 106 of 142: the parts `rows22325R_408` … `rows22325R_411` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 29768 tests: row 116 columns 0–48, row 116 columns 49–54, row 116 columns
55–61, row 116 columns 62–70), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_408 : rowsJ2 116 117 0 49 ≤ 229142125081265 := by decide +kernel

theorem rows22325R_409 : rowsJ2 116 117 49 55 ≤ 63310313262032 := by decide +kernel

theorem rows22325R_410 : rowsJ2 116 117 55 62 ≤ 43384612690515 := by decide +kernel

theorem rows22325R_411 : rowsJ2 116 117 62 71 ≤ 10190601664116 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_408
#print axioms SieveCert.rows22325R_411
