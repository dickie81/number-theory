/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 16–30 of 5066

File 2 of 387: the parts `rows22240R_16` … `rows22240R_30` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 95991 in units of a depth-4 test: row 19 columns 0–13, row 19 columns
14–16, row 19 columns 17–18, row 19 columns 19–339, row 20 columns 0–13, row 20 columns 14–16, row 20 columns 17–18,
row 20 columns 19–19, row 20 columns 20–339, row 21 columns 0–13, row 21 columns 14–16, row 21 columns 17–18, row 21
columns 19–19, row 21 columns 20–20, row 21 columns 21–339), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_16 : rowsJ2 19 20 0 14 ≤ 3919510983341 := by decide +kernel

theorem rows22240R_17 : rowsJ2 19 20 14 17 ≤ 1026381980052 := by decide +kernel

theorem rows22240R_18 : rowsJ2 19 20 17 19 ≤ 1145834301792 := by decide +kernel

theorem rows22240R_19 : rowsJ2 19 20 19 340 ≤ 908199580118 := by decide +kernel

theorem rows22240R_20 : rowsJ2 20 21 0 14 ≤ 3604052535689 := by decide +kernel

theorem rows22240R_21 : rowsJ2 20 21 14 17 ≤ 939230587560 := by decide +kernel

theorem rows22240R_22 : rowsJ2 20 21 17 19 ≤ 1174037884117 := by decide +kernel

theorem rows22240R_23 : rowsJ2 20 21 19 20 ≤ 929294768589 := by decide +kernel

theorem rows22240R_24 : rowsJ2 20 21 20 340 ≤ 1183902527743 := by decide +kernel

theorem rows22240R_25 : rowsJ2 21 22 0 14 ≤ 3299075833575 := by decide +kernel

theorem rows22240R_26 : rowsJ2 21 22 14 17 ≤ 873097969162 := by decide +kernel

theorem rows22240R_27 : rowsJ2 21 22 17 19 ≤ 1208033236231 := by decide +kernel

theorem rows22240R_28 : rowsJ2 21 22 19 20 ≤ 947095064279 := by decide +kernel

theorem rows22240R_29 : rowsJ2 21 22 20 21 ≤ 1207416412663 := by decide +kernel

theorem rows22240R_30 : rowsJ2 21 22 21 340 ≤ 1481182328560 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_16
#print axioms SieveCert.rows22240R_30
