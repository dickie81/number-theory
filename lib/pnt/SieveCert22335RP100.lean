/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 384–386 of 549

File 100 of 140: the parts `rows22335R_384` … `rows22335R_386` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (3 parts, 22525 tests: row 113 columns 0–49, row 113 columns 50–55, row 113 columns
56–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22335R_384 : rowsJ2 113 114 0 50 ≤ 266892053785425 := by decide +kernel

theorem rows22335R_385 : rowsJ2 113 114 50 56 ≤ 51862375980980 := by decide +kernel

theorem rows22335R_386 : rowsJ2 113 114 56 63 ≤ 32213736778160 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_384
#print axioms SieveCert.rows22335R_386
