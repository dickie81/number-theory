/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 31–35 of 561

File 8 of 143: the parts `rows22322R_31` … `rows22322R_35` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 25741 tests: row 44 columns 35–43, row 44 columns 44–299, row 45 columns
0–34, row 45 columns 35–43, row 45 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22322R.lean`.
-/
import SieveGrid22322R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22322R

theorem rows22322R_31 : rowsJ2 44 45 35 44 ≤ 436270898678224 := by decide +kernel

theorem rows22322R_32 : rowsJ2 44 45 44 300 ≤ 59791323146178 := by decide +kernel

theorem rows22322R_33 : rowsJ2 45 46 0 35 ≤ 2047449969842352 := by decide +kernel

theorem rows22322R_34 : rowsJ2 45 46 35 44 ≤ 419906489789259 := by decide +kernel

theorem rows22322R_35 : rowsJ2 45 46 44 300 ≤ 125643712201983 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_31
#print axioms SieveCert.rows22322R_35
