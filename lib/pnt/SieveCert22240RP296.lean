/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3724–3738 of 5066

File 296 of 387: the parts `rows22240R_3724` … `rows22240R_3738` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 99201 in units of a depth-4 test: row 129 columns 77–78, row 129
columns 79–80, row 129 columns 81–83, row 129 columns 84–86, row 129 columns 87–89, row 129 columns 90–339, row 130
columns 0–24, row 130 columns 25–28, row 130 columns 29–35, row 130 columns 36–53, row 130 columns 54–56, row 130
columns 57–58, row 130 columns 59–59, row 130 columns 60–60, row 130 columns 61–61), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3724 : rowsJ2 129 130 77 79 ≤ 4521880428974 := by decide +kernel

theorem rows22240R_3725 : rowsJ2 129 130 79 81 ≤ 2899169497767 := by decide +kernel

theorem rows22240R_3726 : rowsJ2 129 130 81 84 ≤ 6709222641290 := by decide +kernel

theorem rows22240R_3727 : rowsJ2 129 130 84 87 ≤ 14408700121872 := by decide +kernel

theorem rows22240R_3728 : rowsJ2 129 130 87 90 ≤ 26812209510450 := by decide +kernel

theorem rows22240R_3729 : rowsJ2 129 130 90 340 ≤ 793257260019970 := by decide +kernel

theorem rows22240R_3730 : rowsJ2 130 131 0 25 ≤ 4136826701514 := by decide +kernel

theorem rows22240R_3731 : rowsJ2 130 131 25 29 ≤ 16535800277354 := by decide +kernel

theorem rows22240R_3732 : rowsJ2 130 131 29 36 ≤ 11129679573234 := by decide +kernel

theorem rows22240R_3733 : rowsJ2 130 131 36 54 ≤ 3167456621672 := by decide +kernel

theorem rows22240R_3734 : rowsJ2 130 131 54 57 ≤ 6118943718574 := by decide +kernel

theorem rows22240R_3735 : rowsJ2 130 131 57 59 ≤ 6723386237474 := by decide +kernel

theorem rows22240R_3736 : rowsJ2 130 131 59 60 ≤ 4288508660350 := by decide +kernel

theorem rows22240R_3737 : rowsJ2 130 131 60 61 ≤ 4961358906967 := by decide +kernel

theorem rows22240R_3738 : rowsJ2 130 131 61 62 ≤ 5652083731387 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3724
#print axioms SieveCert.rows22240R_3738
