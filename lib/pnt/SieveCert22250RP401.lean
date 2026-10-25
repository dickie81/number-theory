/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4861–4872 of 5796

File 401 of 465: the parts `rows22250R_4861` … `rows22250R_4872` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99059 tests: row 157 columns 61–61, row 157 columns 62–62, row 157 columns
63–63, row 157 columns 64–64, row 157 columns 65–65, row 157 columns 66–66, row 157 columns 67–67, row 157 columns
68–68, row 157 columns 69–69, row 157 columns 70–70, row 157 columns 71–71, row 157 columns 72–73), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4861 : rowsJ2 157 158 61 62 ≤ 13136362610786 := by decide +kernel

theorem rows22250R_4862 : rowsJ2 157 158 62 63 ≤ 13018862518879 := by decide +kernel

theorem rows22250R_4863 : rowsJ2 157 158 63 64 ≤ 11773123764384 := by decide +kernel

theorem rows22250R_4864 : rowsJ2 157 158 64 65 ≤ 10598605572833 := by decide +kernel

theorem rows22250R_4865 : rowsJ2 157 158 65 66 ≤ 9493459317598 := by decide +kernel

theorem rows22250R_4866 : rowsJ2 157 158 66 67 ≤ 8455958803495 := by decide +kernel

theorem rows22250R_4867 : rowsJ2 157 158 67 68 ≤ 7484494809735 := by decide +kernel

theorem rows22250R_4868 : rowsJ2 157 158 68 69 ≤ 6577570098410 := by decide +kernel

theorem rows22250R_4869 : rowsJ2 157 158 69 70 ≤ 5733794857921 := by decide +kernel

theorem rows22250R_4870 : rowsJ2 157 158 70 71 ≤ 4951882554205 := by decide +kernel

theorem rows22250R_4871 : rowsJ2 157 158 71 72 ≤ 4230646165371 := by decide +kernel

theorem rows22250R_4872 : rowsJ2 157 158 72 74 ≤ 6534925305369 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4861
#print axioms SieveCert.rows22250R_4872
