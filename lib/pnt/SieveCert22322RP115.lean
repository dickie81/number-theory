/-
# The refined certificate at `L = 11161/5000` with `n = 300`, parts 442–446 of 561

File 115 of 143: the parts `rows22322R_442` … `rows22322R_446` of `SieveCert22322R.lean`'s certificate on
`SieveGrid22322R.grid22322R` (5 parts, 28844 tests: row 123 columns 63–299, row 124 columns 0–46, row 124 columns
47–53, row 124 columns 54–62, row 124 columns 63–299), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22322R_442 : rowsJ2 123 124 63 300 ≤ 1064481146890817 := by decide +kernel

theorem rows22322R_443 : rowsJ2 124 125 0 47 ≤ 164968412961919 := by decide +kernel

theorem rows22322R_444 : rowsJ2 124 125 47 54 ≤ 93043641294459 := by decide +kernel

theorem rows22322R_445 : rowsJ2 124 125 54 63 ≤ 38776990925188 := by decide +kernel

theorem rows22322R_446 : rowsJ2 124 125 63 300 ≤ 1244594914167969 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22322R_442
#print axioms SieveCert.rows22322R_446
