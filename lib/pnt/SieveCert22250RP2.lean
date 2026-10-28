/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 16–30 of 4715

File 2 of 351: the parts `rows22250R_16` … `rows22250R_30` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 93519 in units of a depth-4 test: row 19 columns 0–13, row 19 columns
14–16, row 19 columns 17–18, row 19 columns 19–339, row 20 columns 0–13, row 20 columns 14–16, row 20 columns 17–18,
row 20 columns 19–19, row 20 columns 20–339, row 21 columns 0–13, row 21 columns 14–16, row 21 columns 17–18, row 21
columns 19–19, row 21 columns 20–20, row 21 columns 21–339), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_16 : rowsJ2 19 20 0 14 ≤ 2528479172344 := by decide +kernel

theorem rows22250R_17 : rowsJ2 19 20 14 17 ≤ 811270198920 := by decide +kernel

theorem rows22250R_18 : rowsJ2 19 20 17 19 ≤ 1469544526862 := by decide +kernel

theorem rows22250R_19 : rowsJ2 19 20 19 340 ≤ 1153491186281 := by decide +kernel

theorem rows22250R_20 : rowsJ2 20 21 0 14 ≤ 2259397949536 := by decide +kernel

theorem rows22250R_21 : rowsJ2 20 21 14 17 ≤ 840180056516 := by decide +kernel

theorem rows22250R_22 : rowsJ2 20 21 17 19 ≤ 1537600244792 := by decide +kernel

theorem rows22250R_23 : rowsJ2 20 21 19 20 ≤ 1200924216314 := by decide +kernel

theorem rows22250R_24 : rowsJ2 20 21 20 340 ≤ 1488169227842 := by decide +kernel

theorem rows22250R_25 : rowsJ2 21 22 0 14 ≤ 2004953490548 := by decide +kernel

theorem rows22250R_26 : rowsJ2 21 22 14 17 ≤ 876916928716 := by decide +kernel

theorem rows22250R_27 : rowsJ2 21 22 17 19 ≤ 1626427552597 := by decide +kernel

theorem rows22250R_28 : rowsJ2 21 22 19 20 ≤ 1248570627751 := by decide +kernel

theorem rows22250R_29 : rowsJ2 21 22 20 21 ≤ 1513049817037 := by decide +kernel

theorem rows22250R_30 : rowsJ2 21 22 21 340 ≤ 1729585619519 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_16
#print axioms SieveCert.rows22250R_30
