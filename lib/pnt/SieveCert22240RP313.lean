/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3958–3973 of 5066

File 313 of 387: the parts `rows22240R_3958` … `rows22240R_3973` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97121 in units of a depth-4 test: row 137 columns 71–71, row 137
columns 72–72, row 137 columns 73–73, row 137 columns 74–74, row 137 columns 75–76, row 137 columns 77–79, row 137
columns 80–83, row 137 columns 84–339, row 138 columns 0–23, row 138 columns 24–45, row 138 columns 46–51, row 138
columns 52–53, row 138 columns 54–54, row 138 columns 55–55, row 138 columns 56–56, row 138 columns 57–57), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3958 : rowsJ2 137 138 71 72 ≤ 5769378027148 := by decide +kernel

theorem rows22240R_3959 : rowsJ2 137 138 72 73 ≤ 5018759636516 := by decide +kernel

theorem rows22240R_3960 : rowsJ2 137 138 73 74 ≤ 4310643623093 := by decide +kernel

theorem rows22240R_3961 : rowsJ2 137 138 74 75 ≤ 3665536647240 := by decide +kernel

theorem rows22240R_3962 : rowsJ2 137 138 75 77 ≤ 5575162418712 := by decide +kernel

theorem rows22240R_3963 : rowsJ2 137 138 77 80 ≤ 4730945757511 := by decide +kernel

theorem rows22240R_3964 : rowsJ2 137 138 80 84 ≤ 9223120651294 := by decide +kernel

theorem rows22240R_3965 : rowsJ2 137 138 84 340 ≤ 618455061097195 := by decide +kernel

theorem rows22240R_3966 : rowsJ2 138 139 0 24 ≤ 6259402581386 := by decide +kernel

theorem rows22240R_3967 : rowsJ2 138 139 24 46 ≤ 4222685849768 := by decide +kernel

theorem rows22240R_3968 : rowsJ2 138 139 46 52 ≤ 7304213519302 := by decide +kernel

theorem rows22240R_3969 : rowsJ2 138 139 52 54 ≤ 6316347807444 := by decide +kernel

theorem rows22240R_3970 : rowsJ2 138 139 54 55 ≤ 4128670898196 := by decide +kernel

theorem rows22240R_3971 : rowsJ2 138 139 55 56 ≤ 4839716286631 := by decide +kernel

theorem rows22240R_3972 : rowsJ2 138 139 56 57 ≤ 5596258289164 := by decide +kernel

theorem rows22240R_3973 : rowsJ2 138 139 57 58 ≤ 6396446695180 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3958
#print axioms SieveCert.rows22240R_3973
