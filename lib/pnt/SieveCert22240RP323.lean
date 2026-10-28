/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4091–4103 of 5066

File 323 of 387: the parts `rows22240R_4091` … `rows22240R_4103` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 92377 in units of a depth-4 test: row 142 columns 63–63, row 142
columns 64–64, row 142 columns 65–65, row 142 columns 66–66, row 142 columns 67–67, row 142 columns 68–68, row 142
columns 69–69, row 142 columns 70–70, row 142 columns 71–71, row 142 columns 72–73, row 142 columns 74–75, row 142
columns 76–79, row 142 columns 80–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4091 : rowsJ2 142 143 63 64 ≤ 12483570177537 := by decide +kernel

theorem rows22240R_4092 : rowsJ2 142 143 64 65 ≤ 11239990520798 := by decide +kernel

theorem rows22240R_4093 : rowsJ2 142 143 65 66 ≤ 10054438195564 := by decide +kernel

theorem rows22240R_4094 : rowsJ2 142 143 66 67 ≤ 8944927533341 := by decide +kernel

theorem rows22240R_4095 : rowsJ2 142 143 67 68 ≤ 7889035140096 := by decide +kernel

theorem rows22240R_4096 : rowsJ2 142 143 68 69 ≤ 6905265630351 := by decide +kernel

theorem rows22240R_4097 : rowsJ2 142 143 69 70 ≤ 5992067042694 := by decide +kernel

theorem rows22240R_4098 : rowsJ2 142 143 70 71 ≤ 5147998353246 := by decide +kernel

theorem rows22240R_4099 : rowsJ2 142 143 71 72 ≤ 4371729975875 := by decide +kernel

theorem rows22240R_4100 : rowsJ2 142 143 72 74 ≤ 6679870389856 := by decide +kernel

theorem rows22240R_4101 : rowsJ2 142 143 74 76 ≤ 4359891458817 := by decide +kernel

theorem rows22240R_4102 : rowsJ2 142 143 76 80 ≤ 3768868445405 := by decide +kernel

theorem rows22240R_4103 : rowsJ2 142 143 80 340 ≤ 1185179770391779 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4091
#print axioms SieveCert.rows22240R_4103
