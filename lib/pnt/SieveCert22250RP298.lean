/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3889–3901 of 4715

File 298 of 351: the parts `rows22250R_3889` … `rows22250R_3901` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 98097 in units of a depth-4 test: row 146 columns 58–58, row 146
columns 59–59, row 146 columns 60–60, row 146 columns 61–61, row 146 columns 62–62, row 146 columns 63–63, row 146
columns 64–64, row 146 columns 65–65, row 146 columns 66–66, row 146 columns 67–67, row 146 columns 68–69, row 146
columns 70–72, row 146 columns 73–77), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3889 : rowsJ2 146 147 58 59 ≤ 13162863442353 := by decide +kernel

theorem rows22250R_3890 : rowsJ2 146 147 59 60 ≤ 14356292949894 := by decide +kernel

theorem rows22250R_3891 : rowsJ2 146 147 60 61 ≤ 12916902506667 := by decide +kernel

theorem rows22250R_3892 : rowsJ2 146 147 61 62 ≤ 11563908025986 := by decide +kernel

theorem rows22250R_3893 : rowsJ2 146 147 62 63 ≤ 10294961332982 := by decide +kernel

theorem rows22250R_3894 : rowsJ2 146 147 63 64 ≤ 9107876744416 := by decide +kernel

theorem rows22250R_3895 : rowsJ2 146 147 64 65 ≤ 8000623512021 := by decide +kernel

theorem rows22250R_3896 : rowsJ2 146 147 65 66 ≤ 6971318938471 := by decide +kernel

theorem rows22250R_3897 : rowsJ2 146 147 66 67 ≤ 6018222119842 := by decide +kernel

theorem rows22250R_3898 : rowsJ2 146 147 67 68 ≤ 5139728274298 := by decide +kernel

theorem rows22250R_3899 : rowsJ2 146 147 68 70 ≤ 7935144395155 := by decide +kernel

theorem rows22250R_3900 : rowsJ2 146 147 70 73 ≤ 7100995429668 := by decide +kernel

theorem rows22250R_3901 : rowsJ2 146 147 73 78 ≤ 3559269927712 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3889
#print axioms SieveCert.rows22250R_3901
