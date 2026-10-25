/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4697–4711 of 4715

File 350 of 351: the parts `rows22250R_4697` … `rows22250R_4711` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 92532 tests: rows 251–252, rows 253–254, rows 255–256, rows 257–258, rows
259–260, rows 261–262, rows 263–264, rows 265–266, rows 267–268, rows 269–270, rows 271–273, rows 274–322, rows
323–325, rows 326–328, rows 329–331), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_4697 : rows2 251 253 ≤ 20147988239032594 := by decide +kernel

theorem rows22250R_4698 : rows2 253 255 ≤ 20268508639328647 := by decide +kernel

theorem rows22250R_4699 : rows2 255 257 ≤ 20396523103790127 := by decide +kernel

theorem rows22250R_4700 : rows2 257 259 ≤ 20524548946388953 := by decide +kernel

theorem rows22250R_4701 : rows2 259 261 ≤ 20644783762477407 := by decide +kernel

theorem rows22250R_4702 : rows2 261 263 ≤ 20771650576164257 := by decide +kernel

theorem rows22250R_4703 : rows2 263 265 ≤ 20897514865022282 := by decide +kernel

theorem rows22250R_4704 : rows2 265 267 ≤ 21014391881960790 := by decide +kernel

theorem rows22250R_4705 : rows2 267 269 ≤ 21136621220067500 := by decide +kernel

theorem rows22250R_4706 : rows2 269 271 ≤ 21256353314556168 := by decide +kernel

theorem rows22250R_4707 : rows2 271 274 ≤ 32158769768147474 := by decide +kernel

theorem rows22250R_4708 : rows2 274 323 ≤ 32240290970985655 := by decide +kernel

theorem rows22250R_4709 : rows2 323 326 ≤ 33564133816170562 := by decide +kernel

theorem rows22250R_4710 : rows2 326 329 ≤ 35195831192367540 := by decide +kernel

theorem rows22250R_4711 : rows2 329 332 ≤ 36902312389942481 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4697
#print axioms SieveCert.rows22250R_4711
