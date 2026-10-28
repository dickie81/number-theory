/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 47–62 of 5066

File 4 of 387: the parts `rows22240R_47` … `rows22240R_62` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96091 in units of a depth-4 test: row 24 columns 14–16, row 24 columns
17–18, row 24 columns 19–19, row 24 columns 20–20, row 24 columns 21–21, row 24 columns 22–22, row 24 columns 23–23,
row 24 columns 24–339, row 25 columns 0–13, row 25 columns 14–16, row 25 columns 17–18, row 25 columns 19–19, row 25
columns 20–20, row 25 columns 21–21, row 25 columns 22–22, row 25 columns 23–23), each a sum of refined costs
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

theorem rows22240R_47 : rowsJ2 24 25 14 17 ≤ 793071095119 := by decide +kernel

theorem rows22240R_48 : rowsJ2 24 25 17 19 ≤ 1339029671534 := by decide +kernel

theorem rows22240R_49 : rowsJ2 24 25 19 20 ≤ 1035206984328 := by decide +kernel

theorem rows22240R_50 : rowsJ2 24 25 20 21 ≤ 1300477454862 := by decide +kernel

theorem rows22240R_51 : rowsJ2 24 25 21 22 ≤ 1532425119152 := by decide +kernel

theorem rows22240R_52 : rowsJ2 24 25 22 23 ≤ 1725139551013 := by decide +kernel

theorem rows22240R_53 : rowsJ2 24 25 23 24 ≤ 1877069361956 := by decide +kernel

theorem rows22240R_54 : rowsJ2 24 25 24 340 ≤ 1988012417349 := by decide +kernel

theorem rows22240R_55 : rowsJ2 25 26 0 14 ≤ 2224417662040 := by decide +kernel

theorem rows22240R_56 : rowsJ2 25 26 14 17 ≤ 806321936518 := by decide +kernel

theorem rows22240R_57 : rowsJ2 25 26 17 19 ≤ 1393958958471 := by decide +kernel

theorem rows22240R_58 : rowsJ2 25 26 19 20 ≤ 1078381127225 := by decide +kernel

theorem rows22240R_59 : rowsJ2 25 26 20 21 ≤ 1326692702828 := by decide +kernel

theorem rows22240R_60 : rowsJ2 25 26 21 22 ≤ 1540147087046 := by decide +kernel

theorem rows22240R_61 : rowsJ2 25 26 22 23 ≤ 1715182005128 := by decide +kernel

theorem rows22240R_62 : rowsJ2 25 26 23 24 ≤ 1852238977543 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_47
#print axioms SieveCert.rows22240R_62
