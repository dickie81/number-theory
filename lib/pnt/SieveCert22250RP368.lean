/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4449–4462 of 5796

File 368 of 465: the parts `rows22250R_4449` … `rows22250R_4462` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 96012 tests: row 143 columns 71–71, row 143 columns 72–72, row 143 columns
73–73, row 143 columns 74–74, row 143 columns 75–75, row 143 columns 76–76, row 143 columns 77–77, row 143 columns
78–78, row 143 columns 79–79, row 143 columns 80–81, row 143 columns 82–83, row 143 columns 84–86, row 143 columns
87–90, row 143 columns 91–359), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4449 : rowsJ2 143 144 71 72 ≤ 7782325089644 := by decide +kernel

theorem rows22250R_4450 : rowsJ2 143 144 72 73 ≤ 7000532054763 := by decide +kernel

theorem rows22250R_4451 : rowsJ2 143 144 73 74 ≤ 6257030441876 := by decide +kernel

theorem rows22250R_4452 : rowsJ2 143 144 74 75 ≤ 5568160331282 := by decide +kernel

theorem rows22250R_4453 : rowsJ2 143 144 75 76 ≤ 4914973577348 := by decide +kernel

theorem rows22250R_4454 : rowsJ2 143 144 76 77 ≤ 4314143329844 := by decide +kernel

theorem rows22250R_4455 : rowsJ2 143 144 77 78 ≤ 3746636234368 := by decide +kernel

theorem rows22250R_4456 : rowsJ2 143 144 78 79 ≤ 3229458232598 := by decide +kernel

theorem rows22250R_4457 : rowsJ2 143 144 79 80 ≤ 2743467793974 := by decide +kernel

theorem rows22250R_4458 : rowsJ2 143 144 80 82 ≤ 4203804074883 := by decide +kernel

theorem rows22250R_4459 : rowsJ2 143 144 82 84 ≤ 2739292578146 := by decide +kernel

theorem rows22250R_4460 : rowsJ2 143 144 84 87 ≤ 2001042627134 := by decide +kernel

theorem rows22250R_4461 : rowsJ2 143 144 87 91 ≤ 11167128863922 := by decide +kernel

theorem rows22250R_4462 : rowsJ2 143 144 91 360 ≤ 401001215868513 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4449
#print axioms SieveCert.rows22250R_4462
