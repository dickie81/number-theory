/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 925–935 of 5796

File 98 of 465: the parts `rows22250R_925` … `rows22250R_935` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98473 tests: row 60 columns 59–59, row 60 columns 60–359, row 61 columns
0–16, row 61 columns 17–21, row 61 columns 22–23, row 61 columns 24–24, row 61 columns 25–25, row 61 columns 26–26,
row 61 columns 27–27, row 61 columns 28–28, row 61 columns 29–29), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_925 : rowsJ2 60 61 59 60 ≤ 11022647965504 := by decide +kernel

theorem rows22250R_926 : rowsJ2 60 61 60 360 ≤ 12294992912147 := by decide +kernel

theorem rows22250R_927 : rowsJ2 61 62 0 17 ≤ 2238673420935 := by decide +kernel

theorem rows22250R_928 : rowsJ2 61 62 17 22 ≤ 594265142516 := by decide +kernel

theorem rows22250R_929 : rowsJ2 61 62 22 24 ≤ 116239219001 := by decide +kernel

theorem rows22250R_930 : rowsJ2 61 62 24 25 ≤ 38685561778 := by decide +kernel

theorem rows22250R_931 : rowsJ2 61 62 25 26 ≤ 28959443726 := by decide +kernel

theorem rows22250R_932 : rowsJ2 61 62 26 27 ≤ 19317802408 := by decide +kernel

theorem rows22250R_933 : rowsJ2 61 62 27 28 ≤ 12855150554 := by decide +kernel

theorem rows22250R_934 : rowsJ2 61 62 28 29 ≤ 6439104457 := by decide +kernel

theorem rows22250R_935 : rowsJ2 61 62 29 30 ≤ 3210292464 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_925
#print axioms SieveCert.rows22250R_935
