/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 528–532 of 561

File 135 of 143: the parts `rows22322R_528` … `rows22322R_532` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 23813 tests: rows 160–160, rows 161–161, rows 162–162, rows 163–163, rows
164–164), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_528 : rows2 160 161 ≤ 3845289702655124 := by decide +kernel

theorem rows22322R_529 : rows2 161 162 ≤ 3992133543944638 := by decide +kernel

theorem rows22322R_530 : rows2 162 163 ≤ 4139336327589451 := by decide +kernel

theorem rows22322R_531 : rows2 163 164 ≤ 4286955381923669 := by decide +kernel

theorem rows22322R_532 : rows2 164 165 ≤ 4434983706551191 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_528
#print axioms SieveCert.rows22322R_532
