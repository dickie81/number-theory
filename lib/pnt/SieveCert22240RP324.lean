/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4104–4116 of 5066

File 324 of 387: the parts `rows22240R_4104` … `rows22240R_4116` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 95742 in units of a depth-4 test: row 143 columns 0–24, row 143 columns
25–47, row 143 columns 48–50, row 143 columns 51–52, row 143 columns 53–53, row 143 columns 54–54, row 143 columns
55–55, row 143 columns 56–56, row 143 columns 57–57, row 143 columns 58–58, row 143 columns 59–59, row 143 columns
60–60, row 143 columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4104 : rowsJ2 143 144 0 25 ≤ 3635698323882 := by decide +kernel

theorem rows22240R_4105 : rowsJ2 143 144 25 48 ≤ 4557475269274 := by decide +kernel

theorem rows22240R_4106 : rowsJ2 143 144 48 51 ≤ 8372301472140 := by decide +kernel

theorem rows22240R_4107 : rowsJ2 143 144 51 53 ≤ 8944240148513 := by decide +kernel

theorem rows22240R_4108 : rowsJ2 143 144 53 54 ≤ 5637512297081 := by decide +kernel

theorem rows22240R_4109 : rowsJ2 143 144 54 55 ≤ 6478910598456 := by decide +kernel

theorem rows22240R_4110 : rowsJ2 143 144 55 56 ≤ 7366202636172 := by decide +kernel

theorem rows22240R_4111 : rowsJ2 143 144 56 57 ≤ 8297598796477 := by decide +kernel

theorem rows22240R_4112 : rowsJ2 143 144 57 58 ≤ 9271427353491 := by decide +kernel

theorem rows22240R_4113 : rowsJ2 143 144 58 59 ≤ 10286126854229 := by decide +kernel

theorem rows22240R_4114 : rowsJ2 143 144 59 60 ≤ 11340233965557 := by decide +kernel

theorem rows22240R_4115 : rowsJ2 143 144 60 61 ≤ 12432383137108 := by decide +kernel

theorem rows22240R_4116 : rowsJ2 143 144 61 62 ≤ 13541722370469 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4104
#print axioms SieveCert.rows22240R_4116
