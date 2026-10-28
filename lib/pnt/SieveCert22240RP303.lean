/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3823–3835 of 5066

File 303 of 387: the parts `rows22240R_3823` … `rows22240R_3835` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 99337 in units of a depth-4 test: row 133 columns 49–53, row 133
columns 54–55, row 133 columns 56–57, row 133 columns 58–58, row 133 columns 59–59, row 133 columns 60–60, row 133
columns 61–61, row 133 columns 62–62, row 133 columns 63–63, row 133 columns 64–64, row 133 columns 65–65, row 133
columns 66–66, row 133 columns 67–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22240R_3823 : rowsJ2 133 134 49 54 ≤ 5449337657109 := by decide +kernel

theorem rows22240R_3824 : rowsJ2 133 134 54 56 ≤ 5270426941310 := by decide +kernel

theorem rows22240R_3825 : rowsJ2 133 134 56 58 ≤ 7639537250334 := by decide +kernel

theorem rows22240R_3826 : rowsJ2 133 134 58 59 ≤ 4820309974281 := by decide +kernel

theorem rows22240R_3827 : rowsJ2 133 134 59 60 ≤ 5543385917209 := by decide +kernel

theorem rows22240R_3828 : rowsJ2 133 134 60 61 ≤ 6306333858505 := by decide +kernel

theorem rows22240R_3829 : rowsJ2 133 134 61 62 ≤ 7086717511738 := by decide +kernel

theorem rows22240R_3830 : rowsJ2 133 134 62 63 ≤ 7821274619317 := by decide +kernel

theorem rows22240R_3831 : rowsJ2 133 134 63 64 ≤ 8488688173183 := by decide +kernel

theorem rows22240R_3832 : rowsJ2 133 134 64 65 ≤ 9109646806195 := by decide +kernel

theorem rows22240R_3833 : rowsJ2 133 134 65 66 ≤ 9662437505683 := by decide +kernel

theorem rows22240R_3834 : rowsJ2 133 134 66 67 ≤ 10167827019350 := by decide +kernel

theorem rows22240R_3835 : rowsJ2 133 134 67 68 ≤ 9876058348252 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3823
#print axioms SieveCert.rows22240R_3835
