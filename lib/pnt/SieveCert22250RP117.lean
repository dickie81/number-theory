/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1302–1310 of 4715

File 117 of 351: the parts `rows22250R_1302` … `rows22250R_1310` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 96190 tests: row 69 columns 55–55, row 69 columns 56–56, row 69 columns
57–57, row 69 columns 58–58, row 69 columns 59–59, row 69 columns 60–60, row 69 columns 61–61, row 69 columns 62–62,
row 69 columns 63–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_1302 : rowsJ2 69 70 55 56 ≤ 6939496994773 := by decide +kernel

theorem rows22250R_1303 : rowsJ2 69 70 56 57 ≤ 6532568545286 := by decide +kernel

theorem rows22250R_1304 : rowsJ2 69 70 57 58 ≤ 6130359678611 := by decide +kernel

theorem rows22250R_1305 : rowsJ2 69 70 58 59 ≤ 5784875777041 := by decide +kernel

theorem rows22250R_1306 : rowsJ2 69 70 59 60 ≤ 5443318484457 := by decide +kernel

theorem rows22250R_1307 : rowsJ2 69 70 60 61 ≤ 5093621133646 := by decide +kernel

theorem rows22250R_1308 : rowsJ2 69 70 61 62 ≤ 4747581902115 := by decide +kernel

theorem rows22250R_1309 : rowsJ2 69 70 62 63 ≤ 4392811644182 := by decide +kernel

theorem rows22250R_1310 : rowsJ2 69 70 63 64 ≤ 4041430483334 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1302
#print axioms SieveCert.rows22250R_1310
