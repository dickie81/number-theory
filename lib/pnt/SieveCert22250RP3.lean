/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 31–46 of 5796

File 3 of 465: the parts `rows22250R_31` … `rows22250R_46` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99700 tests: row 22 columns 0–13, row 22 columns 14–16, row 22 columns
17–18, row 22 columns 19–19, row 22 columns 20–20, row 22 columns 21–21, row 22 columns 22–359, row 23 columns 0–13,
row 23 columns 14–16, row 23 columns 17–18, row 23 columns 19–19, row 23 columns 20–20, row 23 columns 21–21, row 23
columns 22–22, row 23 columns 23–359, row 24 columns 0–13), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_31 : rowsJ2 22 23 0 14 ≤ 1764858896168 := by decide +kernel

theorem rows22250R_32 : rowsJ2 22 23 14 17 ≤ 464526601458 := by decide +kernel

theorem rows22250R_33 : rowsJ2 22 23 17 19 ≤ 914927434240 := by decide +kernel

theorem rows22250R_34 : rowsJ2 22 23 19 20 ≤ 748599853303 := by decide +kernel

theorem rows22250R_35 : rowsJ2 22 23 20 21 ≤ 970523524797 := by decide +kernel

theorem rows22250R_36 : rowsJ2 22 23 21 22 ≤ 1190298083525 := by decide +kernel

theorem rows22250R_37 : rowsJ2 22 23 22 360 ≤ 1382164392348 := by decide +kernel

theorem rows22250R_38 : rowsJ2 23 24 0 14 ≤ 1574823817110 := by decide +kernel

theorem rows22250R_39 : rowsJ2 23 24 14 17 ≤ 476565299750 := by decide +kernel

theorem rows22250R_40 : rowsJ2 23 24 17 19 ≤ 964024168397 := by decide +kernel

theorem rows22250R_41 : rowsJ2 23 24 19 20 ≤ 778815636223 := by decide +kernel

theorem rows22250R_42 : rowsJ2 23 24 20 21 ≤ 1004486671938 := by decide +kernel

theorem rows22250R_43 : rowsJ2 23 24 21 22 ≤ 1214135104821 := by decide +kernel

theorem rows22250R_44 : rowsJ2 23 24 22 23 ≤ 1383403518162 := by decide +kernel

theorem rows22250R_45 : rowsJ2 23 24 23 360 ≤ 1521298214722 := by decide +kernel

theorem rows22250R_46 : rowsJ2 24 25 0 14 ≤ 1395019608340 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_31
#print axioms SieveCert.rows22250R_46
