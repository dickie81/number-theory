/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1696–1713 of 5066

File 156 of 387: the parts `rows22240R_1696` … `rows22240R_1713` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (18 parts, work 97682 in units of a depth-4 test: row 76 columns 67–67, row 76 columns
68–68, row 76 columns 69–69, row 76 columns 70–70, row 76 columns 71–71, row 76 columns 72–73, row 76 columns 74–75,
row 76 columns 76–339, row 77 columns 0–17, row 77 columns 18–19, row 77 columns 20–21, row 77 columns 22–22, row 77
columns 23–23, row 77 columns 24–24, row 77 columns 25–25, row 77 columns 26–26, row 77 columns 27–27, row 77
columns 28–29), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1696 : rowsJ2 76 77 67 68 ≤ 489120644247 := by decide +kernel

theorem rows22240R_1697 : rowsJ2 76 77 68 69 ≤ 368911067919 := by decide +kernel

theorem rows22240R_1698 : rowsJ2 76 77 69 70 ≤ 185763874963 := by decide +kernel

theorem rows22240R_1699 : rowsJ2 76 77 70 71 ≤ 62375893600 := by decide +kernel

theorem rows22240R_1700 : rowsJ2 76 77 71 72 ≤ 0 := by decide +kernel

theorem rows22240R_1701 : rowsJ2 76 77 72 74 ≤ 0 := by decide +kernel

theorem rows22240R_1702 : rowsJ2 76 77 74 76 ≤ 0 := by decide +kernel

theorem rows22240R_1703 : rowsJ2 76 77 76 340 ≤ 72433683073 := by decide +kernel

theorem rows22240R_1704 : rowsJ2 77 78 0 18 ≤ 576922096850 := by decide +kernel

theorem rows22240R_1705 : rowsJ2 77 78 18 20 ≤ 6316783248 := by decide +kernel

theorem rows22240R_1706 : rowsJ2 77 78 20 22 ≤ 28267290363 := by decide +kernel

theorem rows22240R_1707 : rowsJ2 77 78 22 23 ≤ 13791613260 := by decide +kernel

theorem rows22240R_1708 : rowsJ2 77 78 23 24 ≤ 10147640725 := by decide +kernel

theorem rows22240R_1709 : rowsJ2 77 78 24 25 ≤ 7406608999 := by decide +kernel

theorem rows22240R_1710 : rowsJ2 77 78 25 26 ≤ 4672488337 := by decide +kernel

theorem rows22240R_1711 : rowsJ2 77 78 26 27 ≤ 2827570890 := by decide +kernel

theorem rows22240R_1712 : rowsJ2 77 78 27 28 ≤ 974098209 := by decide +kernel

theorem rows22240R_1713 : rowsJ2 77 78 28 30 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1696
#print axioms SieveCert.rows22240R_1713
