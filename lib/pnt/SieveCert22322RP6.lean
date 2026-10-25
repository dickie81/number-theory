/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 24–27 of 561

File 6 of 143: the parts `rows22322R_24` … `rows22322R_27` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27434 tests: row 41 columns 0–34, row 41 columns 35–299, row 42 columns 0–34,
row 42 columns 35–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`,
one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_24 : rowsJ2 41 42 0 35 ≤ 2367082700321242 := by decide +kernel

theorem rows22322R_25 : rowsJ2 41 42 35 300 ≤ 388188133139135 := by decide +kernel

theorem rows22322R_26 : rowsJ2 42 43 0 35 ≤ 2286506481303778 := by decide +kernel

theorem rows22322R_27 : rowsJ2 42 43 35 300 ≤ 420258880999848 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_24
#print axioms SieveCert.rows22322R_27
