/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3594–3607 of 5796

File 309 of 465: the parts `rows22250R_3594` … `rows22250R_3607` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94784 tests: row 116 columns 46–48, row 116 columns 49–53, row 116 columns
54–63, row 116 columns 64–69, row 116 columns 70–74, row 116 columns 75–78, row 116 columns 79–81, row 116 columns
82–83, row 116 columns 84–85, row 116 columns 86–87, row 116 columns 88–89, row 116 columns 90–91, row 116 columns
92–93, row 116 columns 94–95), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3594 : rowsJ2 116 117 46 49 ≤ 4051809516763 := by decide +kernel

theorem rows22250R_3595 : rowsJ2 116 117 49 54 ≤ 403441413153 := by decide +kernel

theorem rows22250R_3596 : rowsJ2 116 117 54 64 ≤ 293462570153 := by decide +kernel

theorem rows22250R_3597 : rowsJ2 116 117 64 70 ≤ 1390560866749 := by decide +kernel

theorem rows22250R_3598 : rowsJ2 116 117 70 75 ≤ 0 := by decide +kernel

theorem rows22250R_3599 : rowsJ2 116 117 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_3600 : rowsJ2 116 117 79 82 ≤ 183974702725 := by decide +kernel

theorem rows22250R_3601 : rowsJ2 116 117 82 84 ≤ 515986043548 := by decide +kernel

theorem rows22250R_3602 : rowsJ2 116 117 84 86 ≤ 327768811715 := by decide +kernel

theorem rows22250R_3603 : rowsJ2 116 117 86 88 ≤ 287838602228 := by decide +kernel

theorem rows22250R_3604 : rowsJ2 116 117 88 90 ≤ 811779723810 := by decide +kernel

theorem rows22250R_3605 : rowsJ2 116 117 90 92 ≤ 1845300078938 := by decide +kernel

theorem rows22250R_3606 : rowsJ2 116 117 92 94 ≤ 3409164588058 := by decide +kernel

theorem rows22250R_3607 : rowsJ2 116 117 94 96 ≤ 5489536472322 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3594
#print axioms SieveCert.rows22250R_3607
