/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3835–3848 of 5796

File 325 of 465: the parts `rows22250R_3835` … `rows22250R_3848` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 95218 tests: row 124 columns 53–62, row 124 columns 63–64, row 124 columns
65–66, row 124 columns 67–68, row 124 columns 69–70, row 124 columns 71–72, row 124 columns 73–74, row 124 columns
75–76, row 124 columns 77–79, row 124 columns 80–82, row 124 columns 83–85, row 124 columns 86–88, row 124 columns
89–91, row 124 columns 92–93), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3835 : rowsJ2 124 125 53 63 ≤ 2035823783988 := by decide +kernel

theorem rows22250R_3836 : rowsJ2 124 125 63 65 ≤ 2392884505498 := by decide +kernel

theorem rows22250R_3837 : rowsJ2 124 125 65 67 ≤ 3251202305289 := by decide +kernel

theorem rows22250R_3838 : rowsJ2 124 125 67 69 ≤ 3709678929901 := by decide +kernel

theorem rows22250R_3839 : rowsJ2 124 125 69 71 ≤ 3757413253232 := by decide +kernel

theorem rows22250R_3840 : rowsJ2 124 125 71 73 ≤ 3380155887497 := by decide +kernel

theorem rows22250R_3841 : rowsJ2 124 125 73 75 ≤ 2559912969694 := by decide +kernel

theorem rows22250R_3842 : rowsJ2 124 125 75 77 ≤ 1274442506709 := by decide +kernel

theorem rows22250R_3843 : rowsJ2 124 125 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_3844 : rowsJ2 124 125 80 83 ≤ 0 := by decide +kernel

theorem rows22250R_3845 : rowsJ2 124 125 83 86 ≤ 0 := by decide +kernel

theorem rows22250R_3846 : rowsJ2 124 125 86 89 ≤ 914999810028 := by decide +kernel

theorem rows22250R_3847 : rowsJ2 124 125 89 92 ≤ 4662850057792 := by decide +kernel

theorem rows22250R_3848 : rowsJ2 124 125 92 94 ≤ 6130765678730 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3835
#print axioms SieveCert.rows22250R_3848
