/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 491–501 of 5066

File 49 of 387: the parts `rows22240R_491` … `rows22240R_501` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 91710 in units of a depth-4 test: row 48 columns 0–13, row 48 columns
14–17, row 48 columns 18–20, row 48 columns 21–23, row 48 columns 24–25, row 48 columns 26–26, row 48 columns 27–27,
row 48 columns 28–28, row 48 columns 29–29, row 48 columns 30–30, row 48 columns 31–31), each a sum of refined costs
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

theorem rows22240R_491 : rowsJ2 48 49 0 14 ≤ 1473522126071 := by decide +kernel

theorem rows22240R_492 : rowsJ2 48 49 14 18 ≤ 2800535843264 := by decide +kernel

theorem rows22240R_493 : rowsJ2 48 49 18 21 ≤ 2047947066892 := by decide +kernel

theorem rows22240R_494 : rowsJ2 48 49 21 24 ≤ 1608722269004 := by decide +kernel

theorem rows22240R_495 : rowsJ2 48 49 24 26 ≤ 812027111456 := by decide +kernel

theorem rows22240R_496 : rowsJ2 48 49 26 27 ≤ 339361283220 := by decide +kernel

theorem rows22240R_497 : rowsJ2 48 49 27 28 ≤ 300020519747 := by decide +kernel

theorem rows22240R_498 : rowsJ2 48 49 28 29 ≤ 272447348315 := by decide +kernel

theorem rows22240R_499 : rowsJ2 48 49 29 30 ≤ 253548980667 := by decide +kernel

theorem rows22240R_500 : rowsJ2 48 49 30 31 ≤ 241431508051 := by decide +kernel

theorem rows22240R_501 : rowsJ2 48 49 31 32 ≤ 213422452567 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_491
#print axioms SieveCert.rows22240R_501
