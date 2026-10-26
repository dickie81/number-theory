/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 206–208 of 561

File 54 of 143: the parts `rows22322R_206` … `rows22322R_208` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22790 tests: row 84 columns 75–79, row 84 columns 80–299, row 85 columns
0–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_206 : rowsJ2 84 85 75 80 ≤ 7803656203106 := by decide +kernel

theorem rows22322R_207 : rowsJ2 84 85 80 300 ≤ 18582394988619 := by decide +kernel

theorem rows22322R_208 : rowsJ2 85 86 0 39 ≤ 658876340980520 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_206
#print axioms SieveCert.rows22322R_208
