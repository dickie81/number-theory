/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1331–1334 of 1732

File 334 of 430: the parts `rows22310R_1331` … `rows22310R_1334` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29808 tests: row 159 columns 73–76, row 159 columns 77–80, row 159 columns
81–85, row 159 columns 86–90), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_1331 : rowsJ2 159 160 73 77 ≤ 18736963534599 := by decide +kernel

theorem rows22310R_1332 : rowsJ2 159 160 77 81 ≤ 11645849257987 := by decide +kernel

theorem rows22310R_1333 : rowsJ2 159 160 81 86 ≤ 7155225834585 := by decide +kernel

theorem rows22310R_1334 : rowsJ2 159 160 86 91 ≤ 1900643838374 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1331
#print axioms SieveCert.rows22310R_1334
