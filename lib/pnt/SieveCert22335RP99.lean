/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 380–383 of 549

File 99 of 140: the parts `rows22335R_380` … `rows22335R_383` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (4 parts, 26756 tests: row 112 columns 50–55, row 112 columns 56–61, row 112 columns
62–69, row 112 columns 70–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_380 : rowsJ2 112 113 50 56 ≤ 47973524408456 := by decide +kernel

theorem rows22335R_381 : rowsJ2 112 113 56 62 ≤ 29066071379831 := by decide +kernel

theorem rows22335R_382 : rowsJ2 112 113 62 70 ≤ 6597827339420 := by decide +kernel

theorem rows22335R_383 : rowsJ2 112 113 70 300 ≤ 219720197699977 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_380
#print axioms SieveCert.rows22335R_383
