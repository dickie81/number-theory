/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 512–515 of 549

File 131 of 140: the parts `rows22335R_512` … `rows22335R_515` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 25469 tests: rows 156–156, rows 157–157, rows 158–158, rows 159–159), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22335R_512 : rows2 156 157 ≤ 3226191352084401 := by decide +kernel

theorem rows22335R_513 : rows2 157 158 ≤ 3314884277905347 := by decide +kernel

theorem rows22335R_514 : rows2 158 159 ≤ 3467794328204370 := by decide +kernel

theorem rows22335R_515 : rows2 159 160 ≤ 3618478616560265 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_512
#print axioms SieveCert.rows22335R_515
