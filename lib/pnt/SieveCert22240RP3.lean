/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 31–46 of 5066

File 3 of 387: the parts `rows22240R_31` … `rows22240R_46` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99700 in units of a depth-4 test: row 22 columns 0–13, row 22 columns
14–16, row 22 columns 17–18, row 22 columns 19–19, row 22 columns 20–20, row 22 columns 21–21, row 22 columns
22–339, row 23 columns 0–13, row 23 columns 14–16, row 23 columns 17–18, row 23 columns 19–19, row 23 columns 20–20,
row 23 columns 21–21, row 23 columns 22–22, row 23 columns 23–339, row 24 columns 0–13), each a sum of refined costs
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

theorem rows22240R_31 : rowsJ2 22 23 0 14 ≤ 3010885580725 := by decide +kernel

theorem rows22240R_32 : rowsJ2 22 23 14 17 ≤ 824778996242 := by decide +kernel

theorem rows22240R_33 : rowsJ2 22 23 17 19 ≤ 1248787171655 := by decide +kernel

theorem rows22240R_34 : rowsJ2 22 23 19 20 ≤ 969561392244 := by decide +kernel

theorem rows22240R_35 : rowsJ2 22 23 20 21 ≤ 1239036419700 := by decide +kernel

theorem rows22240R_36 : rowsJ2 22 23 21 22 ≤ 1499203594548 := by decide +kernel

theorem rows22240R_37 : rowsJ2 22 23 22 340 ≤ 1731584741330 := by decide +kernel

theorem rows22240R_38 : rowsJ2 23 24 0 14 ≤ 2732504283117 := by decide +kernel

theorem rows22240R_39 : rowsJ2 23 24 14 17 ≤ 803714634409 := by decide +kernel

theorem rows22240R_40 : rowsJ2 23 24 17 19 ≤ 1288652907016 := by decide +kernel

theorem rows22240R_41 : rowsJ2 23 24 19 20 ≤ 1000086219268 := by decide +kernel

theorem rows22240R_42 : rowsJ2 23 24 20 21 ≤ 1267502768959 := by decide +kernel

theorem rows22240R_43 : rowsJ2 23 24 21 22 ≤ 1521930776249 := by decide +kernel

theorem rows22240R_44 : rowsJ2 23 24 22 23 ≤ 1726465048344 := by decide +kernel

theorem rows22240R_45 : rowsJ2 23 24 23 340 ≤ 1898925314866 := by decide +kernel

theorem rows22240R_46 : rowsJ2 24 25 0 14 ≤ 2473595771142 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_31
#print axioms SieveCert.rows22240R_46
