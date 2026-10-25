/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 527–529 of 1732

File 133 of 430: the parts `rows22310R_527` … `rows22310R_529` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (3 parts, 22590 tests: row 107 columns 0–34, row 107 columns 35–43, row 107 columns
44–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_527 : rowsJ2 107 108 0 35 ≤ 146138073086389 := by decide +kernel

theorem rows22310R_528 : rowsJ2 107 108 35 44 ≤ 158363456065277 := by decide +kernel

theorem rows22310R_529 : rowsJ2 107 108 44 53 ≤ 247919392054880 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_527
#print axioms SieveCert.rows22310R_529
