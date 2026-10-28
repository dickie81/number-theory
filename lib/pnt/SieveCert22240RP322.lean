/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4078–4090 of 5066

File 322 of 387: the parts `rows22240R_4078` … `rows22240R_4090` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 96074 in units of a depth-4 test: row 142 columns 24–47, row 142
columns 48–50, row 142 columns 51–52, row 142 columns 53–53, row 142 columns 54–54, row 142 columns 55–55, row 142
columns 56–56, row 142 columns 57–57, row 142 columns 58–58, row 142 columns 59–59, row 142 columns 60–60, row 142
columns 61–61, row 142 columns 62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_4078 : rowsJ2 142 143 24 48 ≤ 3821575267081 := by decide +kernel

theorem rows22240R_4079 : rowsJ2 142 143 48 51 ≤ 7388405501574 := by decide +kernel

theorem rows22240R_4080 : rowsJ2 142 143 51 53 ≤ 8099026701650 := by decide +kernel

theorem rows22240R_4081 : rowsJ2 142 143 53 54 ≤ 5159347197549 := by decide +kernel

theorem rows22240R_4082 : rowsJ2 142 143 54 55 ≤ 5964152154972 := by decide +kernel

theorem rows22240R_4083 : rowsJ2 142 143 55 56 ≤ 6815140557845 := by decide +kernel

theorem rows22240R_4084 : rowsJ2 142 143 56 57 ≤ 7710466220608 := by decide +kernel

theorem rows22240R_4085 : rowsJ2 142 143 57 58 ≤ 8648428193071 := by decide +kernel

theorem rows22240R_4086 : rowsJ2 142 143 58 59 ≤ 9627415986704 := by decide +kernel

theorem rows22240R_4087 : rowsJ2 142 143 59 60 ≤ 10645941886661 := by decide +kernel

theorem rows22240R_4088 : rowsJ2 142 143 60 61 ≤ 11702592838500 := by decide +kernel

theorem rows22240R_4089 : rowsJ2 142 143 61 62 ≤ 12776362040464 := by decide +kernel

theorem rows22240R_4090 : rowsJ2 142 143 62 63 ≤ 13807606060531 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4078
#print axioms SieveCert.rows22240R_4090
