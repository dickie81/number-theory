/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 331–334 of 5796

File 28 of 465: the parts `rows22250R_331` … `rows22250R_334` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (4 parts, 88144 tests: row 41 columns 37–37, row 41 columns 38–38, row 41 columns
39–39, row 41 columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_331 : rowsJ2 41 42 37 38 ≤ 411404026353 := by decide +kernel

theorem rows22250R_332 : rowsJ2 41 42 38 39 ≤ 375891247995 := by decide +kernel

theorem rows22250R_333 : rowsJ2 41 42 39 40 ≤ 340564800021 := by decide +kernel

theorem rows22250R_334 : rowsJ2 41 42 40 41 ≤ 299496461201 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_331
#print axioms SieveCert.rows22250R_334
