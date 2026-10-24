/-
# The refined certificate at `L = 4467/2000` with `n = 300`, parts 31–35 of 549

File 8 of 140: the parts `rows22335R_31` … `rows22335R_35` of `SieveCert22335R.lean`'s certificate on
`SieveGrid22335R.grid22335R` (5 parts, 25741 tests: row 44 columns 35–43, row 44 columns 44–299, row 45 columns
0–34, row 45 columns 35–43, row 45 columns 44–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22335R.lean`.
-/
import SieveGrid22335R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22335R

theorem rows22335R_31 : rowsJ2 44 45 35 44 ≤ 405885924538070 := by decide +kernel

theorem rows22335R_32 : rowsJ2 44 45 44 300 ≤ 57369394292675 := by decide +kernel

theorem rows22335R_33 : rowsJ2 45 46 0 35 ≤ 1977368215663830 := by decide +kernel

theorem rows22335R_34 : rowsJ2 45 46 35 44 ≤ 391332033775590 := by decide +kernel

theorem rows22335R_35 : rowsJ2 45 46 44 300 ≤ 121147787177462 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22335R_31
#print axioms SieveCert.rows22335R_35
