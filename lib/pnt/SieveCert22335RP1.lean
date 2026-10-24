/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 0–3 of 549

File 1 of 140: the parts `rows22335R_0` … `rows22335R_3` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27405 tests: rows 0–18, rows 19–22, rows 23–24, rows 25–26), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_0 : rows2 0 19 ≤ 7153387417594325 := by decide +kernel

theorem rows22335R_1 : rows2 19 23 ≤ 5597673418093276 := by decide +kernel

theorem rows22335R_2 : rows2 23 25 ≤ 3599505029714454 := by decide +kernel

theorem rows22335R_3 : rows2 25 27 ≤ 4162272936043793 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_0
#print axioms SieveCert.rows22335R_3
