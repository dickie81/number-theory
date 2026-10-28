/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4184–4195 of 5066

File 330 of 387: the parts `rows22240R_4184` … `rows22240R_4195` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 91629 in units of a depth-4 test: row 146 columns 48–49, row 146
columns 50–51, row 146 columns 52–52, row 146 columns 53–53, row 146 columns 54–54, row 146 columns 55–55, row 146
columns 56–56, row 146 columns 57–57, row 146 columns 58–58, row 146 columns 59–59, row 146 columns 60–60, row 146
columns 61–61), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4184 : rowsJ2 146 147 48 50 ≤ 7206770262581 := by decide +kernel

theorem rows22240R_4185 : rowsJ2 146 147 50 52 ≤ 10219568473510 := by decide +kernel

theorem rows22240R_4186 : rowsJ2 146 147 52 53 ≤ 6371423164769 := by decide +kernel

theorem rows22240R_4187 : rowsJ2 146 147 53 54 ≤ 7278473077234 := by decide +kernel

theorem rows22240R_4188 : rowsJ2 146 147 54 55 ≤ 8232514695963 := by decide +kernel

theorem rows22240R_4189 : rowsJ2 146 147 55 56 ≤ 9231762332052 := by decide +kernel

theorem rows22240R_4190 : rowsJ2 146 147 56 57 ≤ 10274538927886 := by decide +kernel

theorem rows22240R_4191 : rowsJ2 146 147 57 58 ≤ 11359300561254 := by decide +kernel

theorem rows22240R_4192 : rowsJ2 146 147 58 59 ≤ 12484598569585 := by decide +kernel

theorem rows22240R_4193 : rowsJ2 146 147 59 60 ≤ 13649107141597 := by decide +kernel

theorem rows22240R_4194 : rowsJ2 146 147 60 61 ≤ 14851580048854 := by decide +kernel

theorem rows22240R_4195 : rowsJ2 146 147 61 62 ≤ 13395755717466 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4184
#print axioms SieveCert.rows22240R_4195
