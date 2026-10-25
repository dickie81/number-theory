/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2179–2188 of 5796

File 206 of 465: the parts `rows22250R_2179` … `rows22250R_2188` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 99196 tests: row 86 columns 50–50, row 86 columns 51–51, row 86 columns
52–52, row 86 columns 53–53, row 86 columns 54–54, row 86 columns 55–55, row 86 columns 56–56, row 86 columns 57–57,
row 86 columns 58–58, row 86 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2179 : rowsJ2 86 87 50 51 ≤ 635004106368 := by decide +kernel

theorem rows22250R_2180 : rowsJ2 86 87 51 52 ≤ 591780838140 := by decide +kernel

theorem rows22250R_2181 : rowsJ2 86 87 52 53 ≤ 595396885737 := by decide +kernel

theorem rows22250R_2182 : rowsJ2 86 87 53 54 ≤ 458901708710 := by decide +kernel

theorem rows22250R_2183 : rowsJ2 86 87 54 55 ≤ 367451743293 := by decide +kernel

theorem rows22250R_2184 : rowsJ2 86 87 55 56 ≤ 276861177895 := by decide +kernel

theorem rows22250R_2185 : rowsJ2 86 87 56 57 ≤ 231386234282 := by decide +kernel

theorem rows22250R_2186 : rowsJ2 86 87 57 58 ≤ 186329827245 := by decide +kernel

theorem rows22250R_2187 : rowsJ2 86 87 58 59 ≤ 186558931427 := by decide +kernel

theorem rows22250R_2188 : rowsJ2 86 87 59 60 ≤ 140891848468 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2179
#print axioms SieveCert.rows22250R_2188
