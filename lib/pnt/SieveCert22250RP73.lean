/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 678–684 of 5796

File 73 of 465: the parts `rows22250R_678` … `rows22250R_684` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 97124 tests: row 54 columns 31–31, row 54 columns 32–32, row 54 columns
33–33, row 54 columns 34–34, row 54 columns 35–35, row 54 columns 36–36, row 54 columns 37–37), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_678 : rowsJ2 54 55 31 32 ≤ 46600105318 := by decide +kernel

theorem rows22250R_679 : rowsJ2 54 55 32 33 ≤ 36279595276 := by decide +kernel

theorem rows22250R_680 : rowsJ2 54 55 33 34 ≤ 25104059330 := by decide +kernel

theorem rows22250R_681 : rowsJ2 54 55 34 35 ≤ 17931636640 := by decide +kernel

theorem rows22250R_682 : rowsJ2 54 55 35 36 ≤ 9871569948 := by decide +kernel

theorem rows22250R_683 : rowsJ2 54 55 36 37 ≤ 5837722803 := by decide +kernel

theorem rows22250R_684 : rowsJ2 54 55 37 38 ≤ 1344746405 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_678
#print axioms SieveCert.rows22250R_684
