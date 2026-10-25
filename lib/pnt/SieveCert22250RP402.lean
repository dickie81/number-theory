/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4873–4886 of 5796

File 402 of 465: the parts `rows22250R_4873` … `rows22250R_4886` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 90793 tests: row 157 columns 74–75, row 157 columns 76–79, row 157 columns
80–359, row 158 columns 0–44, row 158 columns 45–48, row 158 columns 49–50, row 158 columns 51–51, row 158 columns
52–52, row 158 columns 53–53, row 158 columns 54–54, row 158 columns 55–55, row 158 columns 56–56, row 158 columns
57–57, row 158 columns 58–58), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4873 : rowsJ2 157 158 74 76 ≤ 4352566971413 := by decide +kernel

theorem rows22250R_4874 : rowsJ2 157 158 76 80 ≤ 3956100644060 := by decide +kernel

theorem rows22250R_4875 : rowsJ2 157 158 80 360 ≤ 1693191818788682 := by decide +kernel

theorem rows22250R_4876 : rowsJ2 158 159 0 45 ≤ 2063950995349 := by decide +kernel

theorem rows22250R_4877 : rowsJ2 158 159 45 49 ≤ 8100976348395 := by decide +kernel

theorem rows22250R_4878 : rowsJ2 158 159 49 51 ≤ 7450730297303 := by decide +kernel

theorem rows22250R_4879 : rowsJ2 158 159 51 52 ≤ 4747193130676 := by decide +kernel

theorem rows22250R_4880 : rowsJ2 158 159 52 53 ≤ 5488196980178 := by decide +kernel

theorem rows22250R_4881 : rowsJ2 158 159 53 54 ≤ 6271739459979 := by decide +kernel

theorem rows22250R_4882 : rowsJ2 158 159 54 55 ≤ 7096148544384 := by decide +kernel

theorem rows22250R_4883 : rowsJ2 158 159 55 56 ≤ 7959883468012 := by decide +kernel

theorem rows22250R_4884 : rowsJ2 158 159 56 57 ≤ 8861527836509 := by decide +kernel

theorem rows22250R_4885 : rowsJ2 158 159 57 58 ≤ 9799783331872 := by decide +kernel

theorem rows22250R_4886 : rowsJ2 158 159 58 59 ≤ 10773463974075 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4873
#print axioms SieveCert.rows22250R_4886
