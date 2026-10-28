/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2257–2264 of 4715

File 187 of 351: the parts `rows22250R_2257` … `rows22250R_2264` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, work 91298 in units of a depth-4 test: row 91 columns 82–82, row 91 columns
83–83, row 91 columns 84–84, row 91 columns 85–85, row 91 columns 86–86, row 91 columns 87–87, row 91 columns 88–88,
row 91 columns 89–89), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2257 : rowsJ2 91 92 82 83 ≤ 2207681740371 := by decide +kernel

theorem rows22250R_2258 : rowsJ2 91 92 83 84 ≤ 2962766505817 := by decide +kernel

theorem rows22250R_2259 : rowsJ2 91 92 84 85 ≤ 3877055750435 := by decide +kernel

theorem rows22250R_2260 : rowsJ2 91 92 85 86 ≤ 4982563066847 := by decide +kernel

theorem rows22250R_2261 : rowsJ2 91 92 86 87 ≤ 5980142387356 := by decide +kernel

theorem rows22250R_2262 : rowsJ2 91 92 87 88 ≤ 6030285393425 := by decide +kernel

theorem rows22250R_2263 : rowsJ2 91 92 88 89 ≤ 5325422668547 := by decide +kernel

theorem rows22250R_2264 : rowsJ2 91 92 89 90 ≤ 4710583890358 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2257
#print axioms SieveCert.rows22250R_2264
