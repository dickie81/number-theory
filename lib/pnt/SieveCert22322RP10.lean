/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 40–43 of 561

File 10 of 143: the parts `rows22322R_40` … `rows22322R_43` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (4 parts, 27010 tests: row 47 columns 35–43, row 47 columns 44–299, row 48 columns
0–34, row 48 columns 35–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_40 : rowsJ2 47 48 35 44 ≤ 395257893920880 := by decide +kernel

theorem rows22322R_41 : rowsJ2 47 48 44 300 ≤ 285951676470442 := by decide +kernel

theorem rows22322R_42 : rowsJ2 48 49 0 35 ≤ 1813934966604838 := by decide +kernel

theorem rows22322R_43 : rowsJ2 48 49 35 44 ≤ 387043616841871 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_40
#print axioms SieveCert.rows22322R_43
