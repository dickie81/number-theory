/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 380–382 of 561

File 99 of 143: the parts `rows22322R_380` … `rows22322R_382` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22098 tests: row 110 columns 57–62, row 110 columns 63–69, row 110 columns
70–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_380 : rowsJ2 110 111 57 63 ≤ 23288365256910 := by decide +kernel

theorem rows22322R_381 : rowsJ2 110 111 63 70 ≤ 2575384073617 := by decide +kernel

theorem rows22322R_382 : rowsJ2 110 111 70 300 ≤ 224231769822437 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_380
#print axioms SieveCert.rows22322R_382
