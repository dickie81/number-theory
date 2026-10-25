/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4687–4695 of 5796

File 387 of 465: the parts `rows22250R_4687` … `rows22250R_4695` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 96502 tests: row 151 columns 61–61, row 151 columns 62–62, row 151 columns
63–63, row 151 columns 64–64, row 151 columns 65–65, row 151 columns 66–66, row 151 columns 67–67, row 151 columns
68–68, row 151 columns 69–69), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4687 : rowsJ2 151 152 61 62 ≤ 9205163282813 := by decide +kernel

theorem rows22250R_4688 : rowsJ2 151 152 62 63 ≤ 10096356268551 := by decide +kernel

theorem rows22250R_4689 : rowsJ2 151 152 63 64 ≤ 11018254745227 := by decide +kernel

theorem rows22250R_4690 : rowsJ2 151 152 64 65 ≤ 11937856270695 := by decide +kernel

theorem rows22250R_4691 : rowsJ2 151 152 65 66 ≤ 11801287303615 := by decide +kernel

theorem rows22250R_4692 : rowsJ2 151 152 66 67 ≤ 10700362635380 := by decide +kernel

theorem rows22250R_4693 : rowsJ2 151 152 67 68 ≤ 9647774131783 := by decide +kernel

theorem rows22250R_4694 : rowsJ2 151 152 68 69 ≤ 8658161326888 := by decide +kernel

theorem rows22250R_4695 : rowsJ2 151 152 69 70 ≤ 7713365958323 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4687
#print axioms SieveCert.rows22250R_4695
