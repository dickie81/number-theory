/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2763–2778 of 5796

File 252 of 465: the parts `rows22250R_2763` … `rows22250R_2778` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95931 tests: row 98 columns 54–54, row 98 columns 55–55, row 98 columns
56–56, row 98 columns 57–57, row 98 columns 58–59, row 98 columns 60–61, row 98 columns 62–63, row 98 columns 64–66,
row 98 columns 67–71, row 98 columns 72–76, row 98 columns 77–80, row 98 columns 81–82, row 98 columns 83–83, row 98
columns 84–84, row 98 columns 85–85, row 98 columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2763 : rowsJ2 98 99 54 55 ≤ 1423420063372 := by decide +kernel

theorem rows22250R_2764 : rowsJ2 98 99 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2765 : rowsJ2 98 99 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2766 : rowsJ2 98 99 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2767 : rowsJ2 98 99 58 60 ≤ 0 := by decide +kernel

theorem rows22250R_2768 : rowsJ2 98 99 60 62 ≤ 0 := by decide +kernel

theorem rows22250R_2769 : rowsJ2 98 99 62 64 ≤ 0 := by decide +kernel

theorem rows22250R_2770 : rowsJ2 98 99 64 67 ≤ 0 := by decide +kernel

theorem rows22250R_2771 : rowsJ2 98 99 67 72 ≤ 0 := by decide +kernel

theorem rows22250R_2772 : rowsJ2 98 99 72 77 ≤ 0 := by decide +kernel

theorem rows22250R_2773 : rowsJ2 98 99 77 81 ≤ 52056747568 := by decide +kernel

theorem rows22250R_2774 : rowsJ2 98 99 81 83 ≤ 478594253259 := by decide +kernel

theorem rows22250R_2775 : rowsJ2 98 99 83 84 ≤ 541012992492 := by decide +kernel

theorem rows22250R_2776 : rowsJ2 98 99 84 85 ≤ 822317497171 := by decide +kernel

theorem rows22250R_2777 : rowsJ2 98 99 85 86 ≤ 1152406318677 := by decide +kernel

theorem rows22250R_2778 : rowsJ2 98 99 86 87 ≤ 1542754382016 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2763
#print axioms SieveCert.rows22250R_2778
