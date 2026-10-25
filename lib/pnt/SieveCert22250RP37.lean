/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 396–400 of 5796

File 37 of 465: the parts `rows22250R_396` … `rows22250R_400` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 96462 tests: row 44 columns 34–34, row 44 columns 35–35, row 44 columns
36–36, row 44 columns 37–37, row 44 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_396 : rowsJ2 44 45 34 35 ≤ 296669882305 := by decide +kernel

theorem rows22250R_397 : rowsJ2 44 45 35 36 ≤ 273941712995 := by decide +kernel

theorem rows22250R_398 : rowsJ2 44 45 36 37 ≤ 252894126898 := by decide +kernel

theorem rows22250R_399 : rowsJ2 44 45 37 38 ≤ 220612564129 := by decide +kernel

theorem rows22250R_400 : rowsJ2 44 45 38 39 ≤ 193699144989 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_396
#print axioms SieveCert.rows22250R_400
