/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 332–334 of 549

File 86 of 140: the parts `rows22335R_332` … `rows22335R_334` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22316 tests: row 103 columns 52–58, row 103 columns 59–63, row 103 columns
64–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_332 : rowsJ2 103 104 52 59 ≤ 13776520998159 := by decide +kernel

theorem rows22335R_333 : rowsJ2 103 104 59 64 ≤ 0 := by decide +kernel

theorem rows22335R_334 : rowsJ2 103 104 64 70 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_332
#print axioms SieveCert.rows22335R_334
