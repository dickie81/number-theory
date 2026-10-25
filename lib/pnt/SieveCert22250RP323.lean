/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3805–3818 of 5796

File 323 of 465: the parts `rows22250R_3805` … `rows22250R_3818` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96269 tests: row 123 columns 42–46, row 123 columns 47–59, row 123 columns
60–63, row 123 columns 64–65, row 123 columns 66–67, row 123 columns 68–69, row 123 columns 70–71, row 123 columns
72–73, row 123 columns 74–76, row 123 columns 77–79, row 123 columns 80–82, row 123 columns 83–85, row 123 columns
86–88, row 123 columns 89–91), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_3805 : rowsJ2 123 124 42 47 ≤ 4547529299325 := by decide +kernel

theorem rows22250R_3806 : rowsJ2 123 124 47 60 ≤ 183564168845 := by decide +kernel

theorem rows22250R_3807 : rowsJ2 123 124 60 64 ≤ 2275295710037 := by decide +kernel

theorem rows22250R_3808 : rowsJ2 123 124 64 66 ≤ 2494279693677 := by decide +kernel

theorem rows22250R_3809 : rowsJ2 123 124 66 68 ≤ 3068004515982 := by decide +kernel

theorem rows22250R_3810 : rowsJ2 123 124 68 70 ≤ 3235200899202 := by decide +kernel

theorem rows22250R_3811 : rowsJ2 123 124 70 72 ≤ 2983059791025 := by decide +kernel

theorem rows22250R_3812 : rowsJ2 123 124 72 74 ≤ 2295217992713 := by decide +kernel

theorem rows22250R_3813 : rowsJ2 123 124 74 77 ≤ 1151307062174 := by decide +kernel

theorem rows22250R_3814 : rowsJ2 123 124 77 80 ≤ 0 := by decide +kernel

theorem rows22250R_3815 : rowsJ2 123 124 80 83 ≤ 0 := by decide +kernel

theorem rows22250R_3816 : rowsJ2 123 124 83 86 ≤ 0 := by decide +kernel

theorem rows22250R_3817 : rowsJ2 123 124 86 89 ≤ 819696060374 := by decide +kernel

theorem rows22250R_3818 : rowsJ2 123 124 89 92 ≤ 4296917134339 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3805
#print axioms SieveCert.rows22250R_3818
