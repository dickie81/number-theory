/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1736–1747 of 5796

File 172 of 465: the parts `rows22250R_1736` … `rows22250R_1747` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 96578 tests: row 77 columns 63–63, row 77 columns 64–64, row 77 columns
65–65, row 77 columns 66–66, row 77 columns 67–67, row 77 columns 68–68, row 77 columns 69–69, row 77 columns 70–70,
row 77 columns 71–71, row 77 columns 72–72, row 77 columns 73–73, row 77 columns 74–74), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1736 : rowsJ2 77 78 63 64 ≤ 2353521919411 := by decide +kernel

theorem rows22250R_1737 : rowsJ2 77 78 64 65 ≤ 2121944075662 := by decide +kernel

theorem rows22250R_1738 : rowsJ2 77 78 65 66 ≤ 1884598939145 := by decide +kernel

theorem rows22250R_1739 : rowsJ2 77 78 66 67 ≤ 1649163089268 := by decide +kernel

theorem rows22250R_1740 : rowsJ2 77 78 67 68 ≤ 1459912430167 := by decide +kernel

theorem rows22250R_1741 : rowsJ2 77 78 68 69 ≤ 1272112243400 := by decide +kernel

theorem rows22250R_1742 : rowsJ2 77 78 69 70 ≤ 1130743057377 := by decide +kernel

theorem rows22250R_1743 : rowsJ2 77 78 70 71 ≤ 990420781628 := by decide +kernel

theorem rows22250R_1744 : rowsJ2 77 78 71 72 ≤ 846276012388 := by decide +kernel

theorem rows22250R_1745 : rowsJ2 77 78 72 73 ≤ 703080609613 := by decide +kernel

theorem rows22250R_1746 : rowsJ2 77 78 73 74 ≤ 555826378979 := by decide +kernel

theorem rows22250R_1747 : rowsJ2 77 78 74 75 ≤ 409420892072 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1736
#print axioms SieveCert.rows22250R_1747
