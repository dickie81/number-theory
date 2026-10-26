/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 130–132 of 561

File 34 of 143: the parts `rows22322R_130` … `rows22322R_132` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (3 parts, 22752 tests: row 72 columns 0–34, row 72 columns 35–53, row 72 columns
54–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22322R_130 : rowsJ2 72 73 0 35 ≤ 581586148397303 := by decide +kernel

theorem rows22322R_131 : rowsJ2 72 73 35 54 ≤ 864506955787815 := by decide +kernel

theorem rows22322R_132 : rowsJ2 72 73 54 68 ≤ 197852221739047 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_130
#print axioms SieveCert.rows22322R_132
