/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4887–4897 of 5796

File 403 of 465: the parts `rows22250R_4887` … `rows22250R_4897` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 98717 tests: row 158 columns 59–59, row 158 columns 60–60, row 158 columns
61–61, row 158 columns 62–62, row 158 columns 63–63, row 158 columns 64–64, row 158 columns 65–65, row 158 columns
66–66, row 158 columns 67–67, row 158 columns 68–68, row 158 columns 69–69), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4887 : rowsJ2 158 159 59 60 ≤ 11781490904968 := by decide +kernel

theorem rows22250R_4888 : rowsJ2 158 159 60 61 ≤ 12822887663574 := by decide +kernel

theorem rows22250R_4889 : rowsJ2 158 159 61 62 ≤ 13896775926504 := by decide +kernel

theorem rows22250R_4890 : rowsJ2 158 159 62 63 ≤ 12593495323602 := by decide +kernel

theorem rows22250R_4891 : rowsJ2 158 159 63 64 ≤ 11363702884920 := by decide +kernel

theorem rows22250R_4892 : rowsJ2 158 159 64 65 ≤ 10205436753560 := by decide +kernel

theorem rows22250R_4893 : rowsJ2 158 159 65 66 ≤ 9116864125465 := by decide +kernel

theorem rows22250R_4894 : rowsJ2 158 159 66 67 ≤ 8096275331560 := by decide +kernel

theorem rows22250R_4895 : rowsJ2 158 159 67 68 ≤ 7142078422051 := by decide +kernel

theorem rows22250R_4896 : rowsJ2 158 159 68 69 ≤ 6252794219400 := by decide +kernel

theorem rows22250R_4897 : rowsJ2 158 159 69 70 ≤ 5427051809334 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4887
#print axioms SieveCert.rows22250R_4897
