/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 783–790 of 5796

File 84 of 465: the parts `rows22250R_783` … `rows22250R_790` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 98304 tests: row 57 columns 31–31, row 57 columns 32–32, row 57 columns
33–33, row 57 columns 34–34, row 57 columns 35–35, row 57 columns 36–36, row 57 columns 37–37, row 57 columns
38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_783 : rowsJ2 57 58 31 32 ≤ 14842298296 := by decide +kernel

theorem rows22250R_784 : rowsJ2 57 58 32 33 ≤ 8090147084 := by decide +kernel

theorem rows22250R_785 : rowsJ2 57 58 33 34 ≤ 4470608512 := by decide +kernel

theorem rows22250R_786 : rowsJ2 57 58 34 35 ≤ 870481056 := by decide +kernel

theorem rows22250R_787 : rowsJ2 57 58 35 36 ≤ 433002348 := by decide +kernel

theorem rows22250R_788 : rowsJ2 57 58 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_789 : rowsJ2 57 58 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_790 : rowsJ2 57 58 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_783
#print axioms SieveCert.rows22250R_790
