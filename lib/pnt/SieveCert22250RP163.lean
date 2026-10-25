/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1628–1636 of 5796

File 163 of 465: the parts `rows22250R_1628` … `rows22250R_1636` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 98446 tests: row 75 columns 60–60, row 75 columns 61–61, row 75 columns
62–62, row 75 columns 63–63, row 75 columns 64–64, row 75 columns 65–65, row 75 columns 66–66, row 75 columns 67–67,
row 75 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1628 : rowsJ2 75 76 60 61 ≤ 4203822248655 := by decide +kernel

theorem rows22250R_1629 : rowsJ2 75 76 61 62 ≤ 3927290945534 := by decide +kernel

theorem rows22250R_1630 : rowsJ2 75 76 62 63 ≤ 3653555749497 := by decide +kernel

theorem rows22250R_1631 : rowsJ2 75 76 63 64 ≤ 3373482872208 := by decide +kernel

theorem rows22250R_1632 : rowsJ2 75 76 64 65 ≤ 3096010909261 := by decide +kernel

theorem rows22250R_1633 : rowsJ2 75 76 65 66 ≤ 2811774220774 := by decide +kernel

theorem rows22250R_1634 : rowsJ2 75 76 66 67 ≤ 2529942130991 := by decide +kernel

theorem rows22250R_1635 : rowsJ2 75 76 67 68 ≤ 2294067397826 := by decide +kernel

theorem rows22250R_1636 : rowsJ2 75 76 68 69 ≤ 2060102975894 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1628
#print axioms SieveCert.rows22250R_1636
