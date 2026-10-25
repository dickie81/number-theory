/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2835–2845 of 5796

File 258 of 465: the parts `rows22250R_2835` … `rows22250R_2845` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 99286 tests: row 99 columns 95–95, row 99 columns 96–96, row 99 columns
97–97, row 99 columns 98–98, row 99 columns 99–359, row 100 columns 0–15, row 100 columns 16–20, row 100 columns
21–28, row 100 columns 29–34, row 100 columns 35–37, row 100 columns 38–39), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2835 : rowsJ2 99 100 95 96 ≤ 3287752317586 := by decide +kernel

theorem rows22250R_2836 : rowsJ2 99 100 96 97 ≤ 3297124513177 := by decide +kernel

theorem rows22250R_2837 : rowsJ2 99 100 97 98 ≤ 3365874484196 := by decide +kernel

theorem rows22250R_2838 : rowsJ2 99 100 98 99 ≤ 3509710864359 := by decide +kernel

theorem rows22250R_2839 : rowsJ2 99 100 99 360 ≤ 3717186629953 := by decide +kernel

theorem rows22250R_2840 : rowsJ2 100 101 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2841 : rowsJ2 100 101 16 21 ≤ 0 := by decide +kernel

theorem rows22250R_2842 : rowsJ2 100 101 21 29 ≤ 0 := by decide +kernel

theorem rows22250R_2843 : rowsJ2 100 101 29 35 ≤ 2404792245300 := by decide +kernel

theorem rows22250R_2844 : rowsJ2 100 101 35 38 ≤ 10082164468057 := by decide +kernel

theorem rows22250R_2845 : rowsJ2 100 101 38 40 ≤ 13341345695342 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2835
#print axioms SieveCert.rows22250R_2845
