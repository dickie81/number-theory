/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 902–911 of 4715

File 84 of 351: the parts `rows22250R_902` … `rows22250R_911` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97991 tests: row 60 columns 47–47, row 60 columns 48–48, row 60 columns
49–49, row 60 columns 50–50, row 60 columns 51–51, row 60 columns 52–52, row 60 columns 53–53, row 60 columns 54–54,
row 60 columns 55–55, row 60 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_902 : rowsJ2 60 61 47 48 ≤ 1603034850325 := by decide +kernel

theorem rows22250R_903 : rowsJ2 60 61 48 49 ≤ 2368723993390 := by decide +kernel

theorem rows22250R_904 : rowsJ2 60 61 49 50 ≤ 3239932707503 := by decide +kernel

theorem rows22250R_905 : rowsJ2 60 61 50 51 ≤ 4352424172530 := by decide +kernel

theorem rows22250R_906 : rowsJ2 60 61 51 52 ≤ 5702654932803 := by decide +kernel

theorem rows22250R_907 : rowsJ2 60 61 52 53 ≤ 6998847126715 := by decide +kernel

theorem rows22250R_908 : rowsJ2 60 61 53 54 ≤ 8285115854394 := by decide +kernel

theorem rows22250R_909 : rowsJ2 60 61 54 55 ≤ 9558251087816 := by decide +kernel

theorem rows22250R_910 : rowsJ2 60 61 55 56 ≤ 10868260335659 := by decide +kernel

theorem rows22250R_911 : rowsJ2 60 61 56 57 ≤ 11944691051492 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_902
#print axioms SieveCert.rows22250R_911
