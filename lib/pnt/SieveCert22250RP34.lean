/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 375–378 of 5796

File 34 of 465: the parts `rows22250R_375` … `rows22250R_378` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (4 parts, 82330 tests: row 43 columns 36–36, row 43 columns 37–37, row 43 columns
38–38, row 43 columns 39–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_375 : rowsJ2 43 44 36 37 ≤ 299789374898 := by decide +kernel

theorem rows22250R_376 : rowsJ2 43 44 37 38 ≤ 271390770817 := by decide +kernel

theorem rows22250R_377 : rowsJ2 43 44 38 39 ≤ 237592018181 := by decide +kernel

theorem rows22250R_378 : rowsJ2 43 44 39 40 ≤ 205088778482 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_375
#print axioms SieveCert.rows22250R_378
