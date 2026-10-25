/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 445–449 of 5796

File 44 of 465: the parts `rows22250R_445` … `rows22250R_449` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 92000 tests: row 46 columns 34–34, row 46 columns 35–35, row 46 columns
36–36, row 46 columns 37–37, row 46 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_445 : rowsJ2 46 47 34 35 ≤ 208257292291 := by decide +kernel

theorem rows22250R_446 : rowsJ2 46 47 35 36 ≤ 184018333864 := by decide +kernel

theorem rows22250R_447 : rowsJ2 46 47 36 37 ≤ 161872774626 := by decide +kernel

theorem rows22250R_448 : rowsJ2 46 47 37 38 ≤ 134535080908 := by decide +kernel

theorem rows22250R_449 : rowsJ2 46 47 38 39 ≤ 113639571286 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_445
#print axioms SieveCert.rows22250R_449
