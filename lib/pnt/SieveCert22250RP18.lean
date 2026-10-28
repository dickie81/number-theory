/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 234–242 of 4715

File 18 of 351: the parts `rows22250R_234` … `rows22250R_242` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 96624 in units of a depth-4 test: row 37 columns 35–35, row 37 columns
36–36, row 37 columns 37–339, row 38 columns 0–13, row 38 columns 14–16, row 38 columns 17–19, row 38 columns 20–21,
row 38 columns 22–23, row 38 columns 24–25), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_234 : rowsJ2 37 38 35 36 ≤ 687872271336 := by decide +kernel

theorem rows22250R_235 : rowsJ2 37 38 36 37 ≤ 644220045554 := by decide +kernel

theorem rows22250R_236 : rowsJ2 37 38 37 340 ≤ 593535506814 := by decide +kernel

theorem rows22250R_237 : rowsJ2 38 39 0 14 ≤ 1039613353921 := by decide +kernel

theorem rows22250R_238 : rowsJ2 38 39 14 17 ≤ 2386990588556 := by decide +kernel

theorem rows22250R_239 : rowsJ2 38 39 17 20 ≤ 3088667378066 := by decide +kernel

theorem rows22250R_240 : rowsJ2 38 39 20 22 ≤ 2009721128873 := by decide +kernel

theorem rows22250R_241 : rowsJ2 38 39 22 24 ≤ 1785504199636 := by decide +kernel

theorem rows22250R_242 : rowsJ2 38 39 24 26 ≤ 1500722485975 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_234
#print axioms SieveCert.rows22250R_242
