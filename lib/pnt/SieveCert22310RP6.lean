/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 24–27 of 1732

File 6 of 430: the parts `rows22310R_24` … `rows22310R_27` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 27434 tests: row 41 columns 0–34, row 41 columns 35–399, row 42 columns 0–34,
row 42 columns 35–399), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_24 : rowsJ2 41 42 0 35 ≤ 1468462053654699 := by decide +kernel

theorem rows22310R_25 : rowsJ2 41 42 35 400 ≤ 652933842386931 := by decide +kernel

theorem rows22310R_26 : rowsJ2 42 43 0 35 ≤ 1453076818691832 := by decide +kernel

theorem rows22310R_27 : rowsJ2 42 43 35 400 ≤ 727590556805219 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_24
#print axioms SieveCert.rows22310R_27
