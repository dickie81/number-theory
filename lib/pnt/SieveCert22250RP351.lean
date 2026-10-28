/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4712–4714 of 4715

File 351 of 351: the parts `rows22250R_4712` … `rows22250R_4714` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (3 parts, work 19120 in units of a depth-4 test: rows 332–334, rows 335–336, rows
337–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_4712 : rows2 332 335 ≤ 38821287817239496 := by decide +kernel

theorem rows22250R_4713 : rows2 335 337 ≤ 27007020452835842 := by decide +kernel

theorem rows22250R_4714 : rows2 337 340 ≤ 42333487090397799 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4712
#print axioms SieveCert.rows22250R_4714
