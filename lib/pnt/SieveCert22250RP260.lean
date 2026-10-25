/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2862–2875 of 5796

File 260 of 465: the parts `rows22250R_2862` … `rows22250R_2875` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97684 tests: row 100 columns 56–57, row 100 columns 58–59, row 100 columns
60–61, row 100 columns 62–64, row 100 columns 65–69, row 100 columns 70–74, row 100 columns 75–78, row 100 columns
79–81, row 100 columns 82–83, row 100 columns 84–84, row 100 columns 85–85, row 100 columns 86–86, row 100 columns
87–87, row 100 columns 88–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_2862 : rowsJ2 100 101 56 58 ≤ 659425700909 := by decide +kernel

theorem rows22250R_2863 : rowsJ2 100 101 58 60 ≤ 0 := by decide +kernel

theorem rows22250R_2864 : rowsJ2 100 101 60 62 ≤ 0 := by decide +kernel

theorem rows22250R_2865 : rowsJ2 100 101 62 65 ≤ 0 := by decide +kernel

theorem rows22250R_2866 : rowsJ2 100 101 65 70 ≤ 0 := by decide +kernel

theorem rows22250R_2867 : rowsJ2 100 101 70 75 ≤ 0 := by decide +kernel

theorem rows22250R_2868 : rowsJ2 100 101 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_2869 : rowsJ2 100 101 79 82 ≤ 204815144133 := by decide +kernel

theorem rows22250R_2870 : rowsJ2 100 101 82 84 ≤ 852540798669 := by decide +kernel

theorem rows22250R_2871 : rowsJ2 100 101 84 85 ≤ 811338533269 := by decide +kernel

theorem rows22250R_2872 : rowsJ2 100 101 85 86 ≤ 1134973184275 := by decide +kernel

theorem rows22250R_2873 : rowsJ2 100 101 86 87 ≤ 1520421003635 := by decide +kernel

theorem rows22250R_2874 : rowsJ2 100 101 87 88 ≤ 2022349593585 := by decide +kernel

theorem rows22250R_2875 : rowsJ2 100 101 88 89 ≤ 2661728814469 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2862
#print axioms SieveCert.rows22250R_2875
