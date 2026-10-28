/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 325–331 of 4715

File 29 of 351: the parts `rows22250R_325` … `rows22250R_331` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, work 88752 in units of a depth-4 test: row 42 columns 28–28, row 42 columns
29–29, row 42 columns 30–30, row 42 columns 31–31, row 42 columns 32–32, row 42 columns 33–33, row 42 columns
34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_325 : rowsJ2 42 43 28 29 ≤ 355561531157 := by decide +kernel

theorem rows22250R_326 : rowsJ2 42 43 29 30 ≤ 346871526638 := by decide +kernel

theorem rows22250R_327 : rowsJ2 42 43 30 31 ≤ 360262083971 := by decide +kernel

theorem rows22250R_328 : rowsJ2 42 43 31 32 ≤ 359655359280 := by decide +kernel

theorem rows22250R_329 : rowsJ2 42 43 32 33 ≤ 344879784286 := by decide +kernel

theorem rows22250R_330 : rowsJ2 42 43 33 34 ≤ 316288486794 := by decide +kernel

theorem rows22250R_331 : rowsJ2 42 43 34 35 ≤ 284638168117 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_325
#print axioms SieveCert.rows22250R_331
