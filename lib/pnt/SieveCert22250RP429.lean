/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5237–5249 of 5796

File 429 of 465: the parts `rows22250R_5237` … `rows22250R_5249` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 98023 tests: row 172 columns 47–47, row 172 columns 48–48, row 172 columns
49–49, row 172 columns 50–50, row 172 columns 51–51, row 172 columns 52–52, row 172 columns 53–53, row 172 columns
54–54, row 172 columns 55–55, row 172 columns 56–56, row 172 columns 57–57, row 172 columns 58–58, row 172 columns
59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5237 : rowsJ2 172 173 47 48 ≤ 9045241593373 := by decide +kernel

theorem rows22250R_5238 : rowsJ2 172 173 48 49 ≤ 10137797600988 := by decide +kernel

theorem rows22250R_5239 : rowsJ2 172 173 49 50 ≤ 11277286050744 := by decide +kernel

theorem rows22250R_5240 : rowsJ2 172 173 50 51 ≤ 12462097070154 := by decide +kernel

theorem rows22250R_5241 : rowsJ2 172 173 51 52 ≤ 13690781173234 := by decide +kernel

theorem rows22250R_5242 : rowsJ2 172 173 52 53 ≤ 14962041798916 := by decide +kernel

theorem rows22250R_5243 : rowsJ2 172 173 53 54 ≤ 16274728662802 := by decide +kernel

theorem rows22250R_5244 : rowsJ2 172 173 54 55 ≤ 17627831879946 := by decide +kernel

theorem rows22250R_5245 : rowsJ2 172 173 55 56 ≤ 15964138513461 := by decide +kernel

theorem rows22250R_5246 : rowsJ2 172 173 56 57 ≤ 14396362421811 := by decide +kernel

theorem rows22250R_5247 : rowsJ2 172 173 57 58 ≤ 12921627112812 := by decide +kernel

theorem rows22250R_5248 : rowsJ2 172 173 58 59 ≤ 11537255337044 := by decide +kernel

theorem rows22250R_5249 : rowsJ2 172 173 59 60 ≤ 10240758816058 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5237
#print axioms SieveCert.rows22250R_5249
