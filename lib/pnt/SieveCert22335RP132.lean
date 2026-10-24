/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 516–520 of 549

File 132 of 140: the parts `rows22335R_516` … `rows22335R_520` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 23768 tests: rows 160–160, rows 161–161, rows 162–162, rows 163–163, rows
164–164), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_516 : rows2 160 161 ≤ 3764149713367674 := by decide +kernel

theorem rows22335R_517 : rows2 161 162 ≤ 3907915552614331 := by decide +kernel

theorem rows22335R_518 : rows2 162 163 ≤ 4052022810923290 := by decide +kernel

theorem rows22335R_519 : rows2 163 164 ≤ 4196464118608602 := by decide +kernel

theorem rows22335R_520 : rows2 164 165 ≤ 4341413918593858 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_516
#print axioms SieveCert.rows22335R_520
