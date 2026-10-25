/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 556–561 of 5796

File 59 of 465: the parts `rows22250R_556` … `rows22250R_561` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 95909 tests: row 50 columns 35–35, row 50 columns 36–36, row 50 columns
37–37, row 50 columns 38–38, row 50 columns 39–39, row 50 columns 40–40), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_556 : rowsJ2 50 51 35 36 ≤ 59977406032 := by decide +kernel

theorem rows22250R_557 : rowsJ2 50 51 36 37 ≤ 47898759112 := by decide +kernel

theorem rows22250R_558 : rowsJ2 50 51 37 38 ≤ 34369317853 := by decide +kernel

theorem rows22250R_559 : rowsJ2 50 51 38 39 ≤ 25849509162 := by decide +kernel

theorem rows22250R_560 : rowsJ2 50 51 39 40 ≤ 15840920004 := by decide +kernel

theorem rows22250R_561 : rowsJ2 50 51 40 41 ≤ 10870492055 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_556
#print axioms SieveCert.rows22250R_561
