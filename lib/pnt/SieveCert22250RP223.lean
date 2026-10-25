/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2410–2422 of 5796

File 223 of 465: the parts `rows22250R_2410` … `rows22250R_2422` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99614 tests: row 91 columns 34–37, row 91 columns 38–39, row 91 columns
40–41, row 91 columns 42–42, row 91 columns 43–43, row 91 columns 44–44, row 91 columns 45–45, row 91 columns 46–46,
row 91 columns 47–47, row 91 columns 48–48, row 91 columns 49–49, row 91 columns 50–50, row 91 columns 51–51), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2410 : rowsJ2 91 92 34 38 ≤ 3952862781173 := by decide +kernel

theorem rows22250R_2411 : rowsJ2 91 92 38 40 ≤ 6741942894769 := by decide +kernel

theorem rows22250R_2412 : rowsJ2 91 92 40 42 ≤ 10407235546152 := by decide +kernel

theorem rows22250R_2413 : rowsJ2 91 92 42 43 ≤ 6601645661643 := by decide +kernel

theorem rows22250R_2414 : rowsJ2 91 92 43 44 ≤ 7664161466750 := by decide +kernel

theorem rows22250R_2415 : rowsJ2 91 92 44 45 ≤ 8818698245842 := by decide +kernel

theorem rows22250R_2416 : rowsJ2 91 92 45 46 ≤ 7666432115970 := by decide +kernel

theorem rows22250R_2417 : rowsJ2 91 92 46 47 ≤ 5963324618583 := by decide +kernel

theorem rows22250R_2418 : rowsJ2 91 92 47 48 ≤ 3204395550524 := by decide +kernel

theorem rows22250R_2419 : rowsJ2 91 92 48 49 ≤ 0 := by decide +kernel

theorem rows22250R_2420 : rowsJ2 91 92 49 50 ≤ 0 := by decide +kernel

theorem rows22250R_2421 : rowsJ2 91 92 50 51 ≤ 0 := by decide +kernel

theorem rows22250R_2422 : rowsJ2 91 92 51 52 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2410
#print axioms SieveCert.rows22250R_2422
