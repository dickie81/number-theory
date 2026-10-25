/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 874–883 of 5796

File 93 of 465: the parts `rows22250R_874` … `rows22250R_883` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 90565 tests: row 59 columns 47–47, row 59 columns 48–48, row 59 columns
49–49, row 59 columns 50–50, row 59 columns 51–51, row 59 columns 52–52, row 59 columns 53–53, row 59 columns 54–54,
row 59 columns 55–55, row 59 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_874 : rowsJ2 59 60 47 48 ≤ 113509241432 := by decide +kernel

theorem rows22250R_875 : rowsJ2 59 60 48 49 ≤ 508730139348 := by decide +kernel

theorem rows22250R_876 : rowsJ2 59 60 49 50 ≤ 947321978279 := by decide +kernel

theorem rows22250R_877 : rowsJ2 59 60 50 51 ≤ 1424800259140 := by decide +kernel

theorem rows22250R_878 : rowsJ2 59 60 51 52 ≤ 2050995282042 := by decide +kernel

theorem rows22250R_879 : rowsJ2 59 60 52 53 ≤ 2939503973212 := by decide +kernel

theorem rows22250R_880 : rowsJ2 59 60 53 54 ≤ 3850981577060 := by decide +kernel

theorem rows22250R_881 : rowsJ2 59 60 54 55 ≤ 4782955459715 := by decide +kernel

theorem rows22250R_882 : rowsJ2 59 60 55 56 ≤ 5906094142404 := by decide +kernel

theorem rows22250R_883 : rowsJ2 59 60 56 57 ≤ 7277668646174 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_874
#print axioms SieveCert.rows22250R_883
