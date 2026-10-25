/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5758–5770 of 5796

File 463 of 465: the parts `rows22250R_5758` … `rows22250R_5770` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 94111 tests: rows 231–232, rows 233–234, rows 235–236, rows 237–238, rows
239–240, rows 241–242, rows 243–244, rows 245–246, rows 247–248, rows 249–250, rows 251–252, rows 253–254, rows
255–256), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_5758 : rows2 231 233 ≤ 14505538516745526 := by decide +kernel

theorem rows22250R_5759 : rows2 233 235 ≤ 14824576566083888 := by decide +kernel

theorem rows22250R_5760 : rows2 235 237 ≤ 15165267996850326 := by decide +kernel

theorem rows22250R_5761 : rows2 237 239 ≤ 15523781771380716 := by decide +kernel

theorem rows22250R_5762 : rows2 239 241 ≤ 15896284487748616 := by decide +kernel

theorem rows22250R_5763 : rows2 241 243 ≤ 16283754356647045 := by decide +kernel

theorem rows22250R_5764 : rows2 243 245 ≤ 16687258005232684 := by decide +kernel

theorem rows22250R_5765 : rows2 245 247 ≤ 17107960651086083 := by decide +kernel

theorem rows22250R_5766 : rows2 247 249 ≤ 17547137681005735 := by decide +kernel

theorem rows22250R_5767 : rows2 249 251 ≤ 18006187863622825 := by decide +kernel

theorem rows22250R_5768 : rows2 251 253 ≤ 18099320968379782 := by decide +kernel

theorem rows22250R_5769 : rows2 253 255 ≤ 18191848014337042 := by decide +kernel

theorem rows22250R_5770 : rows2 255 257 ≤ 18283633473392268 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5758
#print axioms SieveCert.rows22250R_5770
