/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4331–4346 of 4715

File 328 of 351: the parts `rows22250R_4331` … `rows22250R_4346` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 98301 in units of a depth-4 test: row 166 columns 58–60, row 166
columns 61–339, row 167 columns 0–37, row 167 columns 38–40, row 167 columns 41–42, row 167 columns 43–43, row 167
columns 44–44, row 167 columns 45–45, row 167 columns 46–46, row 167 columns 47–47, row 167 columns 48–48, row 167
columns 49–49, row 167 columns 50–50, row 167 columns 51–51, row 167 columns 52–52, row 167 columns 53–53), each a
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

theorem rows22250R_4331 : rowsJ2 166 167 58 61 ≤ 15477806988065 := by decide +kernel

theorem rows22250R_4332 : rowsJ2 166 167 61 340 ≤ 2660817696414146 := by decide +kernel

theorem rows22250R_4333 : rowsJ2 167 168 0 38 ≤ 13931856382006 := by decide +kernel

theorem rows22250R_4334 : rowsJ2 167 168 38 41 ≤ 21168311141927 := by decide +kernel

theorem rows22250R_4335 : rowsJ2 167 168 41 43 ≤ 20307340356874 := by decide +kernel

theorem rows22250R_4336 : rowsJ2 167 168 43 44 ≤ 12220685562082 := by decide +kernel

theorem rows22250R_4337 : rowsJ2 167 168 44 45 ≤ 13684745065231 := by decide +kernel

theorem rows22250R_4338 : rowsJ2 167 168 45 46 ≤ 15210366922559 := by decide +kernel

theorem rows22250R_4339 : rowsJ2 167 168 46 47 ≤ 16795482758046 := by decide +kernel

theorem rows22250R_4340 : rowsJ2 167 168 47 48 ≤ 18438268605483 := by decide +kernel

theorem rows22250R_4341 : rowsJ2 167 168 48 49 ≤ 20137133822455 := by decide +kernel

theorem rows22250R_4342 : rowsJ2 167 168 49 50 ≤ 19927442228852 := by decide +kernel

theorem rows22250R_4343 : rowsJ2 167 168 50 51 ≤ 17868201799241 := by decide +kernel

theorem rows22250R_4344 : rowsJ2 167 168 51 52 ≤ 15938851368736 := by decide +kernel

theorem rows22250R_4345 : rowsJ2 167 168 52 53 ≤ 14135235540489 := by decide +kernel

theorem rows22250R_4346 : rowsJ2 167 168 53 54 ≤ 12453513806220 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4331
#print axioms SieveCert.rows22250R_4346
