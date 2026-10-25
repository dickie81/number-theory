/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 269–273 of 5796

File 20 of 465: the parts `rows22250R_269` … `rows22250R_273` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (5 parts, 94306 tests: row 38 columns 35–35, row 38 columns 36–36, row 38 columns
37–37, row 38 columns 38–359, row 39 columns 0–13), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_269 : rowsJ2 38 39 35 36 ≤ 619471359384 := by decide +kernel

theorem rows22250R_270 : rowsJ2 38 39 36 37 ≤ 628142000072 := by decide +kernel

theorem rows22250R_271 : rowsJ2 38 39 37 38 ≤ 612277765962 := by decide +kernel

theorem rows22250R_272 : rowsJ2 38 39 38 360 ≤ 585617167855 := by decide +kernel

theorem rows22250R_273 : rowsJ2 39 40 0 14 ≤ 502501987908 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_269
#print axioms SieveCert.rows22250R_273
