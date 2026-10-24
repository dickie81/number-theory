/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 529–532 of 549

File 135 of 140: the parts `rows22335R_529` … `rows22335R_532` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26253 tests: rows 188–190, rows 191–193, rows 194–196, rows 197–199), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_529 : rows2 188 191 ≤ 23319332574207322 := by decide +kernel

theorem rows22335R_530 : rows2 191 194 ≤ 24206113417503889 := by decide +kernel

theorem rows22335R_531 : rows2 194 197 ≤ 25140988139461289 := by decide +kernel

theorem rows22335R_532 : rows2 197 200 ≤ 26253870278417454 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_529
#print axioms SieveCert.rows22335R_532
