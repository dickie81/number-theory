/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4682–4696 of 4715

File 349 of 351: the parts `rows22250R_4682` … `rows22250R_4696` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 96824 in units of a depth-4 test: rows 221–222, rows 223–224, rows
225–226, rows 227–228, rows 229–230, rows 231–232, rows 233–234, rows 235–236, rows 237–238, rows 239–240, rows
241–242, rows 243–244, rows 245–246, rows 247–248, rows 249–250), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4682 : rows2 221 223 ≤ 15878964611094287 := by decide +kernel

theorem rows22250R_4683 : rows2 223 225 ≤ 16271864276687943 := by decide +kernel

theorem rows22250R_4684 : rows2 225 227 ≤ 16680808425081466 := by decide +kernel

theorem rows22250R_4685 : rows2 227 229 ≤ 17106978037630096 := by decide +kernel

theorem rows22250R_4686 : rows2 229 231 ≤ 17551666569625753 := by decide +kernel

theorem rows22250R_4687 : rows2 231 233 ≤ 18016293612275167 := by decide +kernel

theorem rows22250R_4688 : rows2 233 235 ≤ 18502420547954831 := by decide +kernel

theorem rows22250R_4689 : rows2 235 237 ≤ 19011768542429710 := by decide +kernel

theorem rows22250R_4690 : rows2 237 239 ≤ 19326863854554694 := by decide +kernel

theorem rows22250R_4691 : rows2 239 241 ≤ 19430416225354709 := by decide +kernel

theorem rows22250R_4692 : rows2 241 243 ≤ 19533049289949172 := by decide +kernel

theorem rows22250R_4693 : rows2 243 245 ≤ 19649838074584552 := by decide +kernel

theorem rows22250R_4694 : rows2 245 247 ≤ 19774976484761138 := by decide +kernel

theorem rows22250R_4695 : rows2 247 249 ≤ 19893700235625703 := by decide +kernel

theorem rows22250R_4696 : rows2 249 251 ≤ 20020495615202495 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4682
#print axioms SieveCert.rows22250R_4696
