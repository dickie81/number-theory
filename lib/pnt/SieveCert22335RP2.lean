/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 4–8 of 549

File 2 of 140: the parts `rows22335R_4` … `rows22335R_8` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_4 : rows2 27 28 ≤ 2287417353715665 := by decide +kernel

theorem rows22335R_5 : rows2 28 29 ≤ 2416433008947938 := by decide +kernel

theorem rows22335R_6 : rows2 29 30 ≤ 2535449470518556 := by decide +kernel

theorem rows22335R_7 : rows2 30 31 ≤ 2641224327088584 := by decide +kernel

theorem rows22335R_8 : rows2 31 32 ≤ 2730340486015681 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_4
#print axioms SieveCert.rows22335R_8
