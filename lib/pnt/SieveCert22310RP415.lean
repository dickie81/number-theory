/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1654–1658 of 1732

File 415 of 430: the parts `rows22310R_1654` … `rows22310R_1658` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 29083 tests: rows 226–226, rows 227–227, rows 228–228, rows 229–229, rows
230–230), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1654 : rows2 226 227 ≤ 3785067966558493 := by decide +kernel

theorem rows22310R_1655 : rows2 227 228 ≤ 3868155095387992 := by decide +kernel

theorem rows22310R_1656 : rows2 228 229 ≤ 3951218286292870 := by decide +kernel

theorem rows22310R_1657 : rows2 229 230 ≤ 4034245368563613 := by decide +kernel

theorem rows22310R_1658 : rows2 230 231 ≤ 4117179441238218 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1654
#print axioms SieveCert.rows22310R_1658
