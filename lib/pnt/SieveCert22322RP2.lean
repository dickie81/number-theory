/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 4–8 of 561

File 2 of 143: the parts `rows22322R_4` … `rows22322R_8` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 24955 tests: rows 27–27, rows 28–28, rows 29–29, rows 30–30, rows 31–31),
each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_4 : rows2 27 28 ≤ 2305315581673053 := by decide +kernel

theorem rows22322R_5 : rows2 28 29 ≤ 2438161648538646 := by decide +kernel

theorem rows22322R_6 : rows2 29 30 ≤ 2561710553602493 := by decide +kernel

theorem rows22322R_7 : rows2 30 31 ≤ 2673048776076825 := by decide +kernel

theorem rows22322R_8 : rows2 31 32 ≤ 2768852127376584 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_4
#print axioms SieveCert.rows22322R_8
