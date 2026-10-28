/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1015–1021 of 5066

File 100 of 387: the parts `rows22240R_1015` … `rows22240R_1021` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 92119 in units of a depth-4 test: row 62 columns 53–53, row 62 columns
54–54, row 62 columns 55–55, row 62 columns 56–56, row 62 columns 57–57, row 62 columns 58–58, row 62 columns
59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1015 : rowsJ2 62 63 53 54 ≤ 7108878574016 := by decide +kernel

theorem rows22240R_1016 : rowsJ2 62 63 54 55 ≤ 8262322698795 := by decide +kernel

theorem rows22240R_1017 : rowsJ2 62 63 55 56 ≤ 9330802496451 := by decide +kernel

theorem rows22240R_1018 : rowsJ2 62 63 56 57 ≤ 10502024924867 := by decide +kernel

theorem rows22240R_1019 : rowsJ2 62 63 57 58 ≤ 11444790203082 := by decide +kernel

theorem rows22240R_1020 : rowsJ2 62 63 58 59 ≤ 12205333914947 := by decide +kernel

theorem rows22240R_1021 : rowsJ2 62 63 59 60 ≤ 12943725049119 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1015
#print axioms SieveCert.rows22240R_1021
