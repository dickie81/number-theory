/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 802–811 of 5796

File 86 of 465: the parts `rows22250R_802` … `rows22250R_811` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 96513 tests: row 57 columns 50–50, row 57 columns 51–51, row 57 columns
52–52, row 57 columns 53–53, row 57 columns 54–54, row 57 columns 55–55, row 57 columns 56–56, row 57 columns
57–359, row 58 columns 0–15, row 58 columns 16–20), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_802 : rowsJ2 57 58 50 51 ≤ 1451482225901 := by decide +kernel

theorem rows22250R_803 : rowsJ2 57 58 51 52 ≤ 2089403885341 := by decide +kernel

theorem rows22250R_804 : rowsJ2 57 58 52 53 ≤ 2994551511839 := by decide +kernel

theorem rows22250R_805 : rowsJ2 57 58 53 54 ≤ 3923098185531 := by decide +kernel

theorem rows22250R_806 : rowsJ2 57 58 54 55 ≤ 4872524967981 := by decide +kernel

theorem rows22250R_807 : rowsJ2 57 58 55 56 ≤ 6016696457770 := by decide +kernel

theorem rows22250R_808 : rowsJ2 57 58 56 57 ≤ 7413956179581 := by decide +kernel

theorem rows22250R_809 : rowsJ2 57 58 57 360 ≤ 8879168810703 := by decide +kernel

theorem rows22250R_810 : rowsJ2 58 59 0 16 ≤ 2259645982461 := by decide +kernel

theorem rows22250R_811 : rowsJ2 58 59 16 21 ≤ 1082615270686 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_802
#print axioms SieveCert.rows22250R_811
