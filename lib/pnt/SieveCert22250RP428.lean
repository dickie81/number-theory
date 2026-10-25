/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5222–5236 of 5796

File 428 of 465: the parts `rows22250R_5222` … `rows22250R_5236` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 95156 tests: row 171 columns 56–56, row 171 columns 57–57, row 171 columns
58–58, row 171 columns 59–59, row 171 columns 60–60, row 171 columns 61–61, row 171 columns 62–62, row 171 columns
63–63, row 171 columns 64–65, row 171 columns 66–68, row 171 columns 69–359, row 172 columns 0–40, row 172 columns
41–43, row 172 columns 44–45, row 172 columns 46–46), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_5222 : rowsJ2 171 172 56 57 ≤ 14890041747726 := by decide +kernel

theorem rows22250R_5223 : rowsJ2 171 172 57 58 ≤ 13396765654571 := by decide +kernel

theorem rows22250R_5224 : rowsJ2 171 172 58 59 ≤ 11993370658095 := by decide +kernel

theorem rows22250R_5225 : rowsJ2 171 172 59 60 ≤ 10677347526987 := by decide +kernel

theorem rows22250R_5226 : rowsJ2 171 172 60 61 ≤ 9446365406931 := by decide +kernel

theorem rows22250R_5227 : rowsJ2 171 172 61 62 ≤ 8298263268606 := by decide +kernel

theorem rows22250R_5228 : rowsJ2 171 172 62 63 ≤ 7231042143753 := by decide +kernel

theorem rows22250R_5229 : rowsJ2 171 172 63 64 ≤ 6242858093753 := by decide +kernel

theorem rows22250R_5230 : rowsJ2 171 172 64 66 ≤ 9828979023150 := by decide +kernel

theorem rows22250R_5231 : rowsJ2 171 172 66 69 ≤ 9218048293600 := by decide +kernel

theorem rows22250R_5232 : rowsJ2 171 172 69 360 ≤ 2520240011359346 := by decide +kernel

theorem rows22250R_5233 : rowsJ2 172 173 0 41 ≤ 7578700257092 := by decide +kernel

theorem rows22250R_5234 : rowsJ2 172 173 41 44 ≤ 13125941814433 := by decide +kernel

theorem rows22250R_5235 : rowsJ2 172 173 44 46 ≤ 13076073242234 := by decide +kernel

theorem rows22250R_5236 : rowsJ2 172 173 46 47 ≤ 8001396611083 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5222
#print axioms SieveCert.rows22250R_5236
