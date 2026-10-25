/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4808–4822 of 5796

File 397 of 465: the parts `rows22250R_4808` … `rows22250R_4822` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95052 tests: row 155 columns 66–66, row 155 columns 67–67, row 155 columns
68–68, row 155 columns 69–69, row 155 columns 70–70, row 155 columns 71–71, row 155 columns 72–72, row 155 columns
73–73, row 155 columns 74–75, row 155 columns 76–78, row 155 columns 79–84, row 155 columns 85–359, row 156 columns
0–44, row 156 columns 45–48, row 156 columns 49–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4808 : rowsJ2 155 156 66 67 ≤ 9201672579625 := by decide +kernel

theorem rows22250R_4809 : rowsJ2 155 156 67 68 ≤ 8196577110042 := by decide +kernel

theorem rows22250R_4810 : rowsJ2 155 156 68 69 ≤ 7255332321291 := by decide +kernel

theorem rows22250R_4811 : rowsJ2 155 156 69 70 ≤ 6376512794720 := by decide +kernel

theorem rows22250R_4812 : rowsJ2 155 156 70 71 ≤ 5558794777427 := by decide +kernel

theorem rows22250R_4813 : rowsJ2 155 156 71 72 ≤ 4800952317034 := by decide +kernel

theorem rows22250R_4814 : rowsJ2 155 156 72 73 ≤ 4101853751657 := by decide +kernel

theorem rows22250R_4815 : rowsJ2 155 156 73 74 ≤ 3460458534849 := by decide +kernel

theorem rows22250R_4816 : rowsJ2 155 156 74 76 ≤ 5222869075051 := by decide +kernel

theorem rows22250R_4817 : rowsJ2 155 156 76 79 ≤ 4416190499487 := by decide +kernel

theorem rows22250R_4818 : rowsJ2 155 156 79 85 ≤ 1809515095806 := by decide +kernel

theorem rows22250R_4819 : rowsJ2 155 156 85 360 ≤ 1472484977433037 := by decide +kernel

theorem rows22250R_4820 : rowsJ2 156 157 0 45 ≤ 1233488980023 := by decide +kernel

theorem rows22250R_4821 : rowsJ2 156 157 45 49 ≤ 6020381406784 := by decide +kernel

theorem rows22250R_4822 : rowsJ2 156 157 49 51 ≤ 5996474544996 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4808
#print axioms SieveCert.rows22250R_4822
