/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 786–789 of 1732

File 197 of 430: the parts `rows22310R_786` … `rows22310R_789` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (4 parts, 24120 tests: row 121 columns 79–81, row 121 columns 82–84, row 121 columns
85–86, row 121 columns 87–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_786 : rowsJ2 121 122 79 82 ≤ 0 := by decide +kernel

theorem rows22310R_787 : rowsJ2 121 122 82 85 ≤ 0 := by decide +kernel

theorem rows22310R_788 : rowsJ2 121 122 85 87 ≤ 116889666003 := by decide +kernel

theorem rows22310R_789 : rowsJ2 121 122 87 89 ≤ 483725351584 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_786
#print axioms SieveCert.rows22310R_789
