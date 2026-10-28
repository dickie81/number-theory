/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 720–730 of 4715

File 69 of 351: the parts `rows22250R_720` … `rows22250R_730` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, work 93698 in units of a depth-4 test: row 55 columns 54–54, row 55 columns
55–339, row 56 columns 0–16, row 56 columns 17–21, row 56 columns 22–23, row 56 columns 24–24, row 56 columns 25–25,
row 56 columns 26–26, row 56 columns 27–27, row 56 columns 28–28, row 56 columns 29–29), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_720 : rowsJ2 55 56 54 55 ≤ 10475775636793 := by decide +kernel

theorem rows22250R_721 : rowsJ2 55 56 55 340 ≤ 12206923426440 := by decide +kernel

theorem rows22250R_722 : rowsJ2 56 57 0 17 ≤ 3124502122045 := by decide +kernel

theorem rows22250R_723 : rowsJ2 56 57 17 22 ≤ 831125542064 := by decide +kernel

theorem rows22250R_724 : rowsJ2 56 57 22 24 ≤ 162625661672 := by decide +kernel

theorem rows22250R_725 : rowsJ2 56 57 24 25 ≤ 54136373014 := by decide +kernel

theorem rows22250R_726 : rowsJ2 56 57 25 26 ≤ 41713654563 := by decide +kernel

theorem rows22250R_727 : rowsJ2 56 57 26 27 ≤ 29386052055 := by decide +kernel

theorem rows22250R_728 : rowsJ2 56 57 27 28 ≤ 19166470020 := by decide +kernel

theorem rows22250R_729 : rowsJ2 56 57 28 29 ≤ 9598925196 := by decide +kernel

theorem rows22250R_730 : rowsJ2 56 57 29 30 ≤ 4497001802 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_720
#print axioms SieveCert.rows22250R_730
