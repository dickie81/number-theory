/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 104–106 of 561

File 27 of 143: the parts `rows22322R_104` … `rows22322R_106` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22935 tests: row 65 columns 0–34, row 65 columns 35–45, row 65 columns
46–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_104 : rowsJ2 65 66 0 35 ≤ 763690755312726 := by decide +kernel

theorem rows22322R_105 : rowsJ2 65 66 35 46 ≤ 651326222143596 := by decide +kernel

theorem rows22322R_106 : rowsJ2 65 66 46 300 ≤ 719198478010206 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_104
#print axioms SieveCert.rows22322R_106
