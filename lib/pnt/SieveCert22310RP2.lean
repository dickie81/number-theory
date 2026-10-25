/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 4–8 of 1732

File 2 of 430: the parts `rows22310R_4` … `rows22310R_8` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_4 : rows2 27 28 ≤ 1024285646611754 := by decide +kernel

theorem rows22310R_5 : rows2 28 29 ≤ 1098670650785439 := by decide +kernel

theorem rows22310R_6 : rows2 29 30 ≤ 1174905844533313 := by decide +kernel

theorem rows22310R_7 : rows2 30 31 ≤ 1252902113259953 := by decide +kernel

theorem rows22310R_8 : rows2 31 32 ≤ 1332572134849414 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_4
#print axioms SieveCert.rows22310R_8
