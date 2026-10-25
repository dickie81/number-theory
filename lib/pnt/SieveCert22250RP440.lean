/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5397–5411 of 5796

File 440 of 465: the parts `rows22250R_5397` … `rows22250R_5411` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95422 tests: row 179 columns 50–50, row 179 columns 51–51, row 179 columns
52–52, row 179 columns 53–53, row 179 columns 54–54, row 179 columns 55–55, row 179 columns 56–56, row 179 columns
57–57, row 179 columns 58–58, row 179 columns 59–60, row 179 columns 61–359, row 180 columns 0–38, row 180 columns
39–40, row 180 columns 41–42, row 180 columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_5397 : rowsJ2 179 180 50 51 ≤ 19286639141036 := by decide +kernel

theorem rows22250R_5398 : rowsJ2 179 180 51 52 ≤ 19095301049772 := by decide +kernel

theorem rows22250R_5399 : rowsJ2 179 180 52 53 ≤ 17249954278352 := by decide +kernel

theorem rows22250R_5400 : rowsJ2 179 180 53 54 ≤ 15513853653615 := by decide +kernel

theorem rows22250R_5401 : rowsJ2 179 180 54 55 ≤ 13883583156819 := by decide +kernel

theorem rows22250R_5402 : rowsJ2 179 180 55 56 ≤ 12355972285785 := by decide +kernel

theorem rows22250R_5403 : rowsJ2 179 180 56 57 ≤ 10928082846410 := by decide +kernel

theorem rows22250R_5404 : rowsJ2 179 180 57 58 ≤ 9597196985413 := by decide +kernel

theorem rows22250R_5405 : rowsJ2 179 180 58 59 ≤ 8360806365697 := by decide +kernel

theorem rows22250R_5406 : rowsJ2 179 180 59 61 ≤ 13379069850048 := by decide +kernel

theorem rows22250R_5407 : rowsJ2 179 180 61 360 ≤ 2588095536822638 := by decide +kernel

theorem rows22250R_5408 : rowsJ2 180 181 0 39 ≤ 11908619313753 := by decide +kernel

theorem rows22250R_5409 : rowsJ2 180 181 39 41 ≤ 13123083369193 := by decide +kernel

theorem rows22250R_5410 : rowsJ2 180 181 41 43 ≤ 17486785125932 := by decide +kernel

theorem rows22250R_5411 : rowsJ2 180 181 43 44 ≤ 10529520576616 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5397
#print axioms SieveCert.rows22250R_5411
