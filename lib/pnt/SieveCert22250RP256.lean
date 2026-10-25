/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2811–2826 of 5796

File 256 of 465: the parts `rows22250R_2811` … `rows22250R_2826` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97046 tests: row 99 columns 53–53, row 99 columns 54–54, row 99 columns
55–55, row 99 columns 56–56, row 99 columns 57–58, row 99 columns 59–60, row 99 columns 61–62, row 99 columns 63–65,
row 99 columns 66–70, row 99 columns 71–75, row 99 columns 76–79, row 99 columns 80–82, row 99 columns 83–83, row 99
columns 84–84, row 99 columns 85–85, row 99 columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at
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

theorem rows22250R_2811 : rowsJ2 99 100 53 54 ≤ 3902288823832 := by decide +kernel

theorem rows22250R_2812 : rowsJ2 99 100 54 55 ≤ 2281838201043 := by decide +kernel

theorem rows22250R_2813 : rowsJ2 99 100 55 56 ≤ 856839032282 := by decide +kernel

theorem rows22250R_2814 : rowsJ2 99 100 56 57 ≤ 0 := by decide +kernel

theorem rows22250R_2815 : rowsJ2 99 100 57 59 ≤ 0 := by decide +kernel

theorem rows22250R_2816 : rowsJ2 99 100 59 61 ≤ 0 := by decide +kernel

theorem rows22250R_2817 : rowsJ2 99 100 61 63 ≤ 0 := by decide +kernel

theorem rows22250R_2818 : rowsJ2 99 100 63 66 ≤ 0 := by decide +kernel

theorem rows22250R_2819 : rowsJ2 99 100 66 71 ≤ 0 := by decide +kernel

theorem rows22250R_2820 : rowsJ2 99 100 71 76 ≤ 0 := by decide +kernel

theorem rows22250R_2821 : rowsJ2 99 100 76 80 ≤ 0 := by decide +kernel

theorem rows22250R_2822 : rowsJ2 99 100 80 83 ≤ 527084767749 := by decide +kernel

theorem rows22250R_2823 : rowsJ2 99 100 83 84 ≤ 537377121784 := by decide +kernel

theorem rows22250R_2824 : rowsJ2 99 100 84 85 ≤ 816791123228 := by decide +kernel

theorem rows22250R_2825 : rowsJ2 99 100 85 86 ≤ 1143616019985 := by decide +kernel

theorem rows22250R_2826 : rowsJ2 99 100 86 87 ≤ 1531492073706 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2811
#print axioms SieveCert.rows22250R_2826
