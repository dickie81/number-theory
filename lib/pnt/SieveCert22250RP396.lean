/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4798–4807 of 5796

File 396 of 465: the parts `rows22250R_4798` … `rows22250R_4807` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97047 tests: row 155 columns 56–56, row 155 columns 57–57, row 155 columns
58–58, row 155 columns 59–59, row 155 columns 60–60, row 155 columns 61–61, row 155 columns 62–62, row 155 columns
63–63, row 155 columns 64–64, row 155 columns 65–65), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4798 : rowsJ2 155 156 56 57 ≤ 7160025563992 := by decide +kernel

theorem rows22250R_4799 : rowsJ2 155 156 57 58 ≤ 8002613170125 := by decide +kernel

theorem rows22250R_4800 : rowsJ2 155 156 58 59 ≤ 8880900430952 := by decide +kernel

theorem rows22250R_4801 : rowsJ2 155 156 59 60 ≤ 9793698793506 := by decide +kernel

theorem rows22250R_4802 : rowsJ2 155 156 60 61 ≤ 10739921806039 := by decide +kernel

theorem rows22250R_4803 : rowsJ2 155 156 61 62 ≤ 11718580500617 := by decide +kernel

theorem rows22250R_4804 : rowsJ2 155 156 62 63 ≤ 12728779207482 := by decide +kernel

theorem rows22250R_4805 : rowsJ2 155 156 63 64 ≤ 12615934162949 := by decide +kernel

theorem rows22250R_4806 : rowsJ2 155 156 64 65 ≤ 11409651416798 := by decide +kernel

theorem rows22250R_4807 : rowsJ2 155 156 65 66 ≤ 10272150056120 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4798
#print axioms SieveCert.rows22250R_4807
