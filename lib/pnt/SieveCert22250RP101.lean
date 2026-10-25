/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 958–965 of 5796

File 101 of 465: the parts `rows22250R_958` … `rows22250R_965` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 95320 tests: row 61 columns 52–52, row 61 columns 53–53, row 61 columns
54–54, row 61 columns 55–55, row 61 columns 56–56, row 61 columns 57–57, row 61 columns 58–58, row 61 columns
59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_958 : rowsJ2 61 62 52 53 ≤ 2886443732880 := by decide +kernel

theorem rows22250R_959 : rowsJ2 61 62 53 54 ≤ 3781468485786 := by decide +kernel

theorem rows22250R_960 : rowsJ2 61 62 54 55 ≤ 4696619544370 := by decide +kernel

theorem rows22250R_961 : rowsJ2 61 62 55 56 ≤ 5799484735694 := by decide +kernel

theorem rows22250R_962 : rowsJ2 61 62 56 57 ≤ 7146301296126 := by decide +kernel

theorem rows22250R_963 : rowsJ2 61 62 57 58 ≤ 8483471524286 := by decide +kernel

theorem rows22250R_964 : rowsJ2 61 62 58 59 ≤ 9638937253665 := by decide +kernel

theorem rows22250R_965 : rowsJ2 61 62 59 60 ≤ 10767643446907 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_958
#print axioms SieveCert.rows22250R_965
