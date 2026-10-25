/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 269–272 of 1732

File 67 of 430: the parts `rows22310R_269` … `rows22310R_272` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 23386 tests: row 81 columns 71–80, row 81 columns 81–399, row 82 columns
0–34, row 82 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22310R_269 : rowsJ2 81 82 71 81 ≤ 250014343841646 := by decide +kernel

theorem rows22310R_270 : rowsJ2 81 82 81 400 ≤ 20291852057357 := by decide +kernel

theorem rows22310R_271 : rowsJ2 82 83 0 35 ≤ 662175528304975 := by decide +kernel

theorem rows22310R_272 : rowsJ2 82 83 35 44 ≤ 87261774959887 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_269
#print axioms SieveCert.rows22310R_272
