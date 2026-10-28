/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4315–4330 of 4715

File 327 of 351: the parts `rows22250R_4315` … `rows22250R_4330` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 95793 in units of a depth-4 test: row 166 columns 39–40, row 166
columns 41–42, row 166 columns 43–43, row 166 columns 44–44, row 166 columns 45–45, row 166 columns 46–46, row 166
columns 47–47, row 166 columns 48–48, row 166 columns 49–49, row 166 columns 50–50, row 166 columns 51–51, row 166
columns 52–52, row 166 columns 53–53, row 166 columns 54–54, row 166 columns 55–55, row 166 columns 56–57), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4315 : rowsJ2 166 167 39 41 ≤ 13765577991980 := by decide +kernel

theorem rows22250R_4316 : rowsJ2 166 167 41 43 ≤ 18580807834501 := by decide +kernel

theorem rows22250R_4317 : rowsJ2 166 167 43 44 ≤ 11268518203408 := by decide +kernel

theorem rows22250R_4318 : rowsJ2 166 167 44 45 ≤ 12673486057565 := by decide +kernel

theorem rows22250R_4319 : rowsJ2 166 167 45 46 ≤ 14140034376974 := by decide +kernel

theorem rows22250R_4320 : rowsJ2 166 167 46 47 ≤ 15666003043534 := by decide +kernel

theorem rows22250R_4321 : rowsJ2 166 167 47 48 ≤ 17249475207887 := by decide +kernel

theorem rows22250R_4322 : rowsJ2 166 167 48 49 ≤ 18888765764133 := by decide +kernel

theorem rows22250R_4323 : rowsJ2 166 167 49 50 ≤ 20582411256435 := by decide +kernel

theorem rows22250R_4324 : rowsJ2 166 167 50 51 ≤ 18499435702709 := by decide +kernel

theorem rows22250R_4325 : rowsJ2 166 167 51 52 ≤ 16545645868777 := by decide +kernel

theorem rows22250R_4326 : rowsJ2 166 167 52 53 ≤ 14716856512301 := by decide +kernel

theorem rows22250R_4327 : rowsJ2 166 167 53 54 ≤ 13009195151215 := by decide +kernel

theorem rows22250R_4328 : rowsJ2 166 167 54 55 ≤ 11419084710495 := by decide +kernel

theorem rows22250R_4329 : rowsJ2 166 167 55 56 ≤ 9943227859374 := by decide +kernel

theorem rows22250R_4330 : rowsJ2 166 167 56 58 ≤ 15900994000222 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4315
#print axioms SieveCert.rows22250R_4330
