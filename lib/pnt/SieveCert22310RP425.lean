/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 1707–1711 of 1732

File 425 of 430: the parts `rows22310R_1707` … `rows22310R_1711` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 28013 tests: rows 291–291, rows 292–292, rows 293–293, rows 294–295, rows
296–297), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22310R_1707 : rows2 291 292 ≤ 7551018244177823 := by decide +kernel

theorem rows22310R_1708 : rows2 292 293 ≤ 7509571294095089 := by decide +kernel

theorem rows22310R_1709 : rows2 293 294 ≤ 7587834833823924 := by decide +kernel

theorem rows22310R_1710 : rows2 294 296 ≤ 15159132799689319 := by decide +kernel

theorem rows22310R_1711 : rows2 296 298 ≤ 15225343354269101 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_1707
#print axioms SieveCert.rows22310R_1711
