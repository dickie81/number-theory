/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 444–447 of 561

File 115 of 142: the parts `rows22325R_444` … `rows22325R_447` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (4 parts, 24908 tests: row 124 columns 47–53, row 124 columns 54–62, row 124 columns
63–299, row 125 columns 0–45), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_444 : rowsJ2 124 125 47 54 ≤ 92780074225151 := by decide +kernel

theorem rows22325R_445 : rowsJ2 124 125 54 63 ≤ 38668293904605 := by decide +kernel

theorem rows22325R_446 : rowsJ2 124 125 63 300 ≤ 1243526998228913 := by decide +kernel

theorem rows22325R_447 : rowsJ2 125 126 0 46 ≤ 150574994478051 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_444
#print axioms SieveCert.rows22325R_447
