/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3687–3700 of 5796

File 315 of 465: the parts `rows22250R_3687` … `rows22250R_3700` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98297 tests: row 119 columns 37–38, row 119 columns 39–40, row 119 columns
41–42, row 119 columns 43–45, row 119 columns 46–50, row 119 columns 51–61, row 119 columns 62–66, row 119 columns
67–69, row 119 columns 70–73, row 119 columns 74–77, row 119 columns 78–80, row 119 columns 81–82, row 119 columns
83–85, row 119 columns 86–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3687 : rowsJ2 119 120 37 39 ≤ 17347285849429 := by decide +kernel

theorem rows22250R_3688 : rowsJ2 119 120 39 41 ≤ 13485428902604 := by decide +kernel

theorem rows22250R_3689 : rowsJ2 119 120 41 43 ≤ 8780811769575 := by decide +kernel

theorem rows22250R_3690 : rowsJ2 119 120 43 46 ≤ 6982671311291 := by decide +kernel

theorem rows22250R_3691 : rowsJ2 119 120 46 51 ≤ 1712817006689 := by decide +kernel

theorem rows22250R_3692 : rowsJ2 119 120 51 62 ≤ 174597593238 := by decide +kernel

theorem rows22250R_3693 : rowsJ2 119 120 62 67 ≤ 2710224702182 := by decide +kernel

theorem rows22250R_3694 : rowsJ2 119 120 67 70 ≤ 2087911277399 := by decide +kernel

theorem rows22250R_3695 : rowsJ2 119 120 70 74 ≤ 725491393066 := by decide +kernel

theorem rows22250R_3696 : rowsJ2 119 120 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_3697 : rowsJ2 119 120 78 81 ≤ 45580445213 := by decide +kernel

theorem rows22250R_3698 : rowsJ2 119 120 81 83 ≤ 114375974294 := by decide +kernel

theorem rows22250R_3699 : rowsJ2 119 120 83 86 ≤ 34766517141 := by decide +kernel

theorem rows22250R_3700 : rowsJ2 119 120 86 89 ≤ 539107981786 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3687
#print axioms SieveCert.rows22250R_3700
