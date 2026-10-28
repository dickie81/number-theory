/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4496–4509 of 5066

File 352 of 387: the parts `rows22240R_4496` … `rows22240R_4509` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96439 in units of a depth-4 test: row 159 columns 0–40, row 159 columns
41–43, row 159 columns 44–45, row 159 columns 46–46, row 159 columns 47–47, row 159 columns 48–48, row 159 columns
49–49, row 159 columns 50–50, row 159 columns 51–51, row 159 columns 52–52, row 159 columns 53–53, row 159 columns
54–54, row 159 columns 55–55, row 159 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4496 : rowsJ2 159 160 0 41 ≤ 8503332573896 := by decide +kernel

theorem rows22240R_4497 : rowsJ2 159 160 41 44 ≤ 13682488880977 := by decide +kernel

theorem rows22240R_4498 : rowsJ2 159 160 44 46 ≤ 13906907533427 := by decide +kernel

theorem rows22240R_4499 : rowsJ2 159 160 46 47 ≤ 8581302907659 := by decide +kernel

theorem rows22240R_4500 : rowsJ2 159 160 47 48 ≤ 9745513645157 := by decide +kernel

theorem rows22240R_4501 : rowsJ2 159 160 48 49 ≤ 10965988393451 := by decide +kernel

theorem rows22240R_4502 : rowsJ2 159 160 49 50 ≤ 12240682142623 := by decide +kernel

theorem rows22240R_4503 : rowsJ2 159 160 50 51 ≤ 13567741634399 := by decide +kernel

theorem rows22240R_4504 : rowsJ2 159 160 51 52 ≤ 14945471939557 := by decide +kernel

theorem rows22240R_4505 : rowsJ2 159 160 52 53 ≤ 16372340654843 := by decide +kernel

theorem rows22240R_4506 : rowsJ2 159 160 53 54 ≤ 17846979796603 := by decide +kernel

theorem rows22240R_4507 : rowsJ2 159 160 54 55 ≤ 17669797860214 := by decide +kernel

theorem rows22240R_4508 : rowsJ2 159 160 55 56 ≤ 15889484235044 := by decide +kernel

theorem rows22240R_4509 : rowsJ2 159 160 56 57 ≤ 14217934846479 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4496
#print axioms SieveCert.rows22240R_4509
