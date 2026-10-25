/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5679–5694 of 5796

File 458 of 465: the parts `rows22250R_5679` … `rows22250R_5694` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98873 tests: row 197 columns 43–359, row 198 columns 0–32, row 198 columns
33–35, row 198 columns 36–37, row 198 columns 38–38, row 198 columns 39–39, row 198 columns 40–40, row 198 columns
41–41, row 198 columns 42–359, row 199 columns 0–32, row 199 columns 33–34, row 199 columns 35–36, row 199 columns
37–37, row 199 columns 38–38, row 199 columns 39–39, row 199 columns 40–40), each a sum of refined costs (`rows2` or
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

theorem rows22250R_5679 : rowsJ2 197 198 43 360 ≤ 3762843370706688 := by decide +kernel

theorem rows22250R_5680 : rowsJ2 198 199 0 33 ≤ 14944532706979 := by decide +kernel

theorem rows22250R_5681 : rowsJ2 198 199 33 36 ≤ 29660291288889 := by decide +kernel

theorem rows22250R_5682 : rowsJ2 198 199 36 38 ≤ 33238946964332 := by decide +kernel

theorem rows22250R_5683 : rowsJ2 198 199 38 39 ≤ 21569609708786 := by decide +kernel

theorem rows22250R_5684 : rowsJ2 198 199 39 40 ≤ 25328137657242 := by decide +kernel

theorem rows22250R_5685 : rowsJ2 198 199 40 41 ≤ 27518774397127 := by decide +kernel

theorem rows22250R_5686 : rowsJ2 198 199 41 42 ≤ 29666078959693 := by decide +kernel

theorem rows22250R_5687 : rowsJ2 198 199 42 360 ≤ 3880314769245478 := by decide +kernel

theorem rows22250R_5688 : rowsJ2 199 200 0 33 ≤ 17501902336428 := by decide +kernel

theorem rows22250R_5689 : rowsJ2 199 200 33 35 ≤ 19129092331840 := by decide +kernel

theorem rows22250R_5690 : rowsJ2 199 200 35 37 ≤ 29647608612014 := by decide +kernel

theorem rows22250R_5691 : rowsJ2 199 200 37 38 ≤ 19524690317620 := by decide +kernel

theorem rows22250R_5692 : rowsJ2 199 200 38 39 ≤ 23112266586981 := by decide +kernel

theorem rows22250R_5693 : rowsJ2 199 200 39 40 ≤ 27002991881355 := by decide +kernel

theorem rows22250R_5694 : rowsJ2 199 200 40 41 ≤ 29165038902591 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5679
#print axioms SieveCert.rows22250R_5694
