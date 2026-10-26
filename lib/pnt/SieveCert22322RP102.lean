/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 390–393 of 561

File 102 of 143: the parts `rows22322R_390` … `rows22322R_393` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 28755 tests: row 112 columns 56–61, row 112 columns 62–69, row 112 columns
70–299, row 113 columns 0–49), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22322R_390 : rowsJ2 112 113 56 62 ≤ 31954800794549 := by decide +kernel

theorem rows22322R_391 : rowsJ2 112 113 62 70 ≤ 7579229152984 := by decide +kernel

theorem rows22322R_392 : rowsJ2 112 113 70 300 ≤ 111505167078894 := by decide +kernel

theorem rows22322R_393 : rowsJ2 113 114 0 50 ≤ 268289931264420 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_390
#print axioms SieveCert.rows22322R_393
