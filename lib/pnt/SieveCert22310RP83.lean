/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 333–336 of 1732

File 83 of 430: the parts `rows22310R_333` … `rows22310R_336` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 28112 tests: row 89 columns 70–84, row 89 columns 85–399, row 90 columns
0–34, row 90 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_333 : rowsJ2 89 90 70 85 ≤ 257243840179160 := by decide +kernel

theorem rows22310R_334 : rowsJ2 89 90 85 400 ≤ 48768878513089 := by decide +kernel

theorem rows22310R_335 : rowsJ2 90 91 0 35 ≤ 459796218492574 := by decide +kernel

theorem rows22310R_336 : rowsJ2 90 91 35 44 ≤ 56643596189072 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_333
#print axioms SieveCert.rows22310R_336
