/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 399–402 of 549

File 104 of 140: the parts `rows22335R_399` … `rows22335R_402` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 29578 tests: row 116 columns 0–48, row 116 columns 49–54, row 116 columns
55–61, row 116 columns 62–71), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_399 : rowsJ2 116 117 0 49 ≤ 228877767121628 := by decide +kernel

theorem rows22335R_400 : rowsJ2 116 117 49 55 ≤ 61396343040889 := by decide +kernel

theorem rows22335R_401 : rowsJ2 116 117 55 62 ≤ 38696314305766 := by decide +kernel

theorem rows22335R_402 : rowsJ2 116 117 62 72 ≤ 7868683831466 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_399
#print axioms SieveCert.rows22335R_402
