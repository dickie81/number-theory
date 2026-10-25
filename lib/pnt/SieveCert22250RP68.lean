/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 707–719 of 4715

File 68 of 351: the parts `rows22250R_707` … `rows22250R_719` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 97653 tests: row 55 columns 41–41, row 55 columns 42–42, row 55 columns
43–43, row 55 columns 44–44, row 55 columns 45–45, row 55 columns 46–46, row 55 columns 47–47, row 55 columns 48–48,
row 55 columns 49–49, row 55 columns 50–50, row 55 columns 51–51, row 55 columns 52–52, row 55 columns 53–53), each
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

theorem rows22250R_707 : rowsJ2 55 56 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_708 : rowsJ2 55 56 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_709 : rowsJ2 55 56 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_710 : rowsJ2 55 56 44 45 ≤ 72315420981 := by decide +kernel

theorem rows22250R_711 : rowsJ2 55 56 45 46 ≤ 283838197084 := by decide +kernel

theorem rows22250R_712 : rowsJ2 55 56 46 47 ≤ 846788309704 := by decide +kernel

theorem rows22250R_713 : rowsJ2 55 56 47 48 ≤ 1681590232453 := by decide +kernel

theorem rows22250R_714 : rowsJ2 55 56 48 49 ≤ 2484801331576 := by decide +kernel

theorem rows22250R_715 : rowsJ2 55 56 49 50 ≤ 3398702900086 := by decide +kernel

theorem rows22250R_716 : rowsJ2 55 56 50 51 ≤ 4565711078916 := by decide +kernel

theorem rows22250R_717 : rowsJ2 55 56 51 52 ≤ 5982108768312 := by decide +kernel

theorem rows22250R_718 : rowsJ2 55 56 52 53 ≤ 7341819776610 := by decide +kernel

theorem rows22250R_719 : rowsJ2 55 56 53 54 ≤ 8791320863437 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_707
#print axioms SieveCert.rows22250R_719
