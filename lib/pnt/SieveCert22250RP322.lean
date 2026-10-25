/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4238–4252 of 4715

File 322 of 351: the parts `rows22250R_4238` … `rows22250R_4252` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96300 tests: row 162 columns 40–42, row 162 columns 43–44, row 162 columns
45–45, row 162 columns 46–46, row 162 columns 47–47, row 162 columns 48–48, row 162 columns 49–49, row 162 columns
50–50, row 162 columns 51–51, row 162 columns 52–52, row 162 columns 53–53, row 162 columns 54–54, row 162 columns
55–55, row 162 columns 56–56, row 162 columns 57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_4238 : rowsJ2 162 163 40 43 ≤ 17566343641209 := by decide +kernel

theorem rows22250R_4239 : rowsJ2 162 163 43 45 ≤ 17167909924531 := by decide +kernel

theorem rows22250R_4240 : rowsJ2 162 163 45 46 ≤ 10416210542869 := by decide +kernel

theorem rows22250R_4241 : rowsJ2 162 163 46 47 ≤ 11718136726663 := by decide +kernel

theorem rows22250R_4242 : rowsJ2 162 163 47 48 ≤ 13077501538936 := by decide +kernel

theorem rows22250R_4243 : rowsJ2 162 163 48 49 ≤ 14492279183102 := by decide +kernel

theorem rows22250R_4244 : rowsJ2 162 163 49 50 ≤ 15960660708083 := by decide +kernel

theorem rows22250R_4245 : rowsJ2 162 163 50 51 ≤ 17481043664987 := by decide +kernel

theorem rows22250R_4246 : rowsJ2 162 163 51 52 ≤ 19052022980334 := by decide +kernel

theorem rows22250R_4247 : rowsJ2 162 163 52 53 ≤ 17128005903089 := by decide +kernel

theorem rows22250R_4248 : rowsJ2 162 163 53 54 ≤ 15322439445093 := by decide +kernel

theorem rows22250R_4249 : rowsJ2 162 163 54 55 ≤ 13631625636936 := by decide +kernel

theorem rows22250R_4250 : rowsJ2 162 163 55 56 ≤ 12052138298279 := by decide +kernel

theorem rows22250R_4251 : rowsJ2 162 163 56 57 ≤ 10580808510859 := by decide +kernel

theorem rows22250R_4252 : rowsJ2 162 163 57 58 ≤ 9214711479280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4238
#print axioms SieveCert.rows22250R_4252
