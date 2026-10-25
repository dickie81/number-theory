/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 594–597 of 1732

File 150 of 430: the parts `rows22310R_594` … `rows22310R_597` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 29960 tests: row 111 columns 0–34, row 111 columns 35–43, row 111 columns
44–56, row 111 columns 57–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_594 : rowsJ2 111 112 0 35 ≤ 112583926066393 := by decide +kernel

theorem rows22310R_595 : rowsJ2 111 112 35 44 ≤ 191110745763802 := by decide +kernel

theorem rows22310R_596 : rowsJ2 111 112 44 57 ≤ 289121162564617 := by decide +kernel

theorem rows22310R_597 : rowsJ2 111 112 57 78 ≤ 180539998430776 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_594
#print axioms SieveCert.rows22310R_597
