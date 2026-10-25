/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2715–2730 of 5796

File 248 of 465: the parts `rows22250R_2715` … `rows22250R_2730` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94776 tests: row 97 columns 55–55, row 97 columns 56–56, row 97 columns
57–57, row 97 columns 58–58, row 97 columns 59–60, row 97 columns 61–62, row 97 columns 63–64, row 97 columns 65–67,
row 97 columns 68–71, row 97 columns 72–76, row 97 columns 77–80, row 97 columns 81–82, row 97 columns 83–83, row 97
columns 84–84, row 97 columns 85–85, row 97 columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_2715 : rowsJ2 97 98 55 56 ≤ 0 := by decide +kernel

theorem rows22250R_2716 : rowsJ2 97 98 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2717 : rowsJ2 97 98 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_2718 : rowsJ2 97 98 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_2719 : rowsJ2 97 98 59 61 ≤ 0 := by decide +kernel

theorem rows22250R_2720 : rowsJ2 97 98 61 63 ≤ 0 := by decide +kernel

theorem rows22250R_2721 : rowsJ2 97 98 63 65 ≤ 0 := by decide +kernel

theorem rows22250R_2722 : rowsJ2 97 98 65 68 ≤ 0 := by decide +kernel

theorem rows22250R_2723 : rowsJ2 97 98 68 72 ≤ 0 := by decide +kernel

theorem rows22250R_2724 : rowsJ2 97 98 72 77 ≤ 0 := by decide +kernel

theorem rows22250R_2725 : rowsJ2 97 98 77 81 ≤ 52411360602 := by decide +kernel

theorem rows22250R_2726 : rowsJ2 97 98 81 83 ≤ 481854460004 := by decide +kernel

theorem rows22250R_2727 : rowsJ2 97 98 83 84 ≤ 544698398651 := by decide +kernel

theorem rows22250R_2728 : rowsJ2 97 98 84 85 ≤ 827919162950 := by decide +kernel

theorem rows22250R_2729 : rowsJ2 97 98 85 86 ≤ 1160218513030 := by decide +kernel

theorem rows22250R_2730 : rowsJ2 97 98 86 87 ≤ 1554201496767 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2715
#print axioms SieveCert.rows22250R_2730
