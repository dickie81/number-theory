/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1563–1572 of 5796

File 157 of 465: the parts `rows22250R_1563` … `rows22250R_1572` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97819 tests: row 74 columns 47–47, row 74 columns 48–48, row 74 columns
49–49, row 74 columns 50–50, row 74 columns 51–51, row 74 columns 52–52, row 74 columns 53–53, row 74 columns 54–54,
row 74 columns 55–55, row 74 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_1563 : rowsJ2 74 75 47 48 ≤ 99755962711 := by decide +kernel

theorem rows22250R_1564 : rowsJ2 74 75 48 49 ≤ 447090159101 := by decide +kernel

theorem rows22250R_1565 : rowsJ2 74 75 49 50 ≤ 832540282618 := by decide +kernel

theorem rows22250R_1566 : rowsJ2 74 75 50 51 ≤ 1252165195803 := by decide +kernel

theorem rows22250R_1567 : rowsJ2 74 75 51 52 ≤ 1802487676744 := by decide +kernel

theorem rows22250R_1568 : rowsJ2 74 75 52 53 ≤ 2583340748685 := by decide +kernel

theorem rows22250R_1569 : rowsJ2 74 75 53 54 ≤ 3225677891752 := by decide +kernel

theorem rows22250R_1570 : rowsJ2 74 75 54 55 ≤ 3729727626742 := by decide +kernel

theorem rows22250R_1571 : rowsJ2 74 75 55 56 ≤ 4207065398702 := by decide +kernel

theorem rows22250R_1572 : rowsJ2 74 75 56 57 ≤ 4749883053768 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1563
#print axioms SieveCert.rows22250R_1572
