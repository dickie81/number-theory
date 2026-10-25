/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 629–640 of 5796

File 68 of 465: the parts `rows22250R_629` … `rows22250R_640` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 94103 tests: row 52 columns 47–47, row 52 columns 48–48, row 52 columns
49–49, row 52 columns 50–50, row 52 columns 51–51, row 52 columns 52–359, row 53 columns 0–14, row 53 columns 15–19,
row 53 columns 20–22, row 53 columns 23–24, row 53 columns 25–25, row 53 columns 26–26), each a sum of refined costs
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

theorem rows22250R_629 : rowsJ2 52 53 47 48 ≤ 121314491913 := by decide +kernel

theorem rows22250R_630 : rowsJ2 52 53 48 49 ≤ 543712014967 := by decide +kernel

theorem rows22250R_631 : rowsJ2 52 53 49 50 ≤ 1012462800594 := by decide +kernel

theorem rows22250R_632 : rowsJ2 52 53 50 51 ≤ 1522773981534 := by decide +kernel

theorem rows22250R_633 : rowsJ2 52 53 51 52 ≤ 2192028132859 := by decide +kernel

theorem rows22250R_634 : rowsJ2 52 53 52 360 ≤ 3141633460764 := by decide +kernel

theorem rows22250R_635 : rowsJ2 53 54 0 15 ≤ 1931663513502 := by decide +kernel

theorem rows22250R_636 : rowsJ2 53 54 15 20 ≤ 2036834378536 := by decide +kernel

theorem rows22250R_637 : rowsJ2 53 54 20 23 ≤ 819651461923 := by decide +kernel

theorem rows22250R_638 : rowsJ2 53 54 23 25 ≤ 389324072746 := by decide +kernel

theorem rows22250R_639 : rowsJ2 53 54 25 26 ≤ 155955961601 := by decide +kernel

theorem rows22250R_640 : rowsJ2 53 54 26 27 ≤ 132058196946 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_629
#print axioms SieveCert.rows22250R_640
