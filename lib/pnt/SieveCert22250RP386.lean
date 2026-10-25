/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4673–4686 of 5796

File 386 of 465: the parts `rows22250R_4673` … `rows22250R_4686` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 92266 tests: row 150 columns 77–78, row 150 columns 79–81, row 150 columns
82–87, row 150 columns 88–359, row 151 columns 0–24, row 151 columns 25–49, row 151 columns 50–52, row 151 columns
53–54, row 151 columns 55–55, row 151 columns 56–56, row 151 columns 57–57, row 151 columns 58–58, row 151 columns
59–59, row 151 columns 60–60), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4673 : rowsJ2 150 151 77 79 ≤ 4381131926213 := by decide +kernel

theorem rows22250R_4674 : rowsJ2 150 151 79 82 ≤ 3589284854063 := by decide +kernel

theorem rows22250R_4675 : rowsJ2 150 151 82 88 ≤ 2707175294124 := by decide +kernel

theorem rows22250R_4676 : rowsJ2 150 151 88 360 ≤ 1012078248432532 := by decide +kernel

theorem rows22250R_4677 : rowsJ2 151 152 0 25 ≤ 1098862477141 := by decide +kernel

theorem rows22250R_4678 : rowsJ2 151 152 25 50 ≤ 3667497499999 := by decide +kernel

theorem rows22250R_4679 : rowsJ2 151 152 50 53 ≤ 6756716933318 := by decide +kernel

theorem rows22250R_4680 : rowsJ2 151 152 53 55 ≤ 7231011586285 := by decide +kernel

theorem rows22250R_4681 : rowsJ2 151 152 55 56 ≤ 4561955813763 := by decide +kernel

theorem rows22250R_4682 : rowsJ2 151 152 56 57 ≤ 5245899658944 := by decide +kernel

theorem rows22250R_4683 : rowsJ2 151 152 57 58 ≤ 5967614986418 := by decide +kernel

theorem rows22250R_4684 : rowsJ2 151 152 58 59 ≤ 6725670914878 := by decide +kernel

theorem rows22250R_4685 : rowsJ2 151 152 59 60 ≤ 7518744710018 := by decide +kernel

theorem rows22250R_4686 : rowsJ2 151 152 60 61 ≤ 8345616306114 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4673
#print axioms SieveCert.rows22250R_4686
