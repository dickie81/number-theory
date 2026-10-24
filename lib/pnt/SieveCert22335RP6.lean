/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 24–27 of 549

File 6 of 140: the parts `rows22335R_24` … `rows22335R_27` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 27434 tests: row 41 columns 0–34, row 41 columns 35–299, row 42 columns 0–34,
row 42 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_24 : rowsJ2 41 42 0 35 ≤ 2298664731388030 := by decide +kernel

theorem rows22335R_25 : rowsJ2 41 42 35 300 ≤ 359833913758339 := by decide +kernel

theorem rows22335R_26 : rowsJ2 42 43 0 35 ≤ 2217716031138939 := by decide +kernel

theorem rows22335R_27 : rowsJ2 42 43 35 300 ≤ 389827383274756 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_24
#print axioms SieveCert.rows22335R_27
