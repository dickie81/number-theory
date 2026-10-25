/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 92–95 of 1732

File 23 of 430: the parts `rows22310R_92` … `rows22310R_95` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23740 tests: row 59 columns 55–58, row 59 columns 59–399, row 60 columns
0–34, row 60 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_92 : rowsJ2 59 60 55 59 ≤ 118796595367615 := by decide +kernel

theorem rows22310R_93 : rowsJ2 59 60 59 400 ≤ 32703932912224 := by decide +kernel

theorem rows22310R_94 : rowsJ2 60 61 0 35 ≤ 1165626019087077 := by decide +kernel

theorem rows22310R_95 : rowsJ2 60 61 35 44 ≤ 422247274570120 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_92
#print axioms SieveCert.rows22310R_95
