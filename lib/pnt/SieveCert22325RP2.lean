/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 4–8 of 561

File 2 of 142: the parts `rows22325R_4` … `rows22325R_8` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_4 : rows2 27 28 ≤ 2290431392252968 := by decide +kernel

theorem rows22325R_5 : rows2 28 29 ≤ 2419600964514086 := by decide +kernel

theorem rows22325R_6 : rows2 29 30 ≤ 2538758819194485 := by decide +kernel

theorem rows22325R_7 : rows2 30 31 ≤ 2644658827677737 := by decide +kernel

theorem rows22325R_8 : rows2 31 32 ≤ 2733879891387489 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_4
#print axioms SieveCert.rows22325R_8
