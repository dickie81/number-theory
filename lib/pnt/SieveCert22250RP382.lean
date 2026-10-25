/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4626–4634 of 5796

File 382 of 465: the parts `rows22250R_4626` … `rows22250R_4634` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 95483 tests: row 149 columns 60–60, row 149 columns 61–61, row 149 columns
62–62, row 149 columns 63–63, row 149 columns 64–64, row 149 columns 65–65, row 149 columns 66–66, row 149 columns
67–67, row 149 columns 68–68), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4626 : rowsJ2 149 150 60 61 ≤ 7293583884020 := by decide +kernel

theorem rows22250R_4627 : rowsJ2 149 150 61 62 ≤ 8096497716216 := by decide +kernel

theorem rows22250R_4628 : rowsJ2 149 150 62 63 ≤ 8931229480100 := by decide +kernel

theorem rows22250R_4629 : rowsJ2 149 150 63 64 ≤ 9796776955405 := by decide +kernel

theorem rows22250R_4630 : rowsJ2 149 150 64 65 ≤ 10659752466283 := by decide +kernel

theorem rows22250R_4631 : rowsJ2 149 150 65 66 ≤ 11471126413307 := by decide +kernel

theorem rows22250R_4632 : rowsJ2 149 150 66 67 ≤ 11322014325802 := by decide +kernel

theorem rows22250R_4633 : rowsJ2 149 150 67 68 ≤ 10270620450677 := by decide +kernel

theorem rows22250R_4634 : rowsJ2 149 150 68 69 ≤ 9282260329936 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4626
#print axioms SieveCert.rows22250R_4634
