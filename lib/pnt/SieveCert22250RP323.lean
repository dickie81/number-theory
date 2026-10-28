/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4253–4268 of 4715

File 323 of 351: the parts `rows22250R_4253` … `rows22250R_4268` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 98413 in units of a depth-4 test: row 162 columns 58–59, row 162
columns 60–61, row 162 columns 62–120, row 162 columns 121–339, row 163 columns 0–39, row 163 columns 40–41, row 163
columns 42–43, row 163 columns 44–44, row 163 columns 45–45, row 163 columns 46–46, row 163 columns 47–47, row 163
columns 48–48, row 163 columns 49–49, row 163 columns 50–50, row 163 columns 51–51, row 163 columns 52–52), each a
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

theorem rows22250R_4253 : rowsJ2 162 163 58 60 ≤ 14738821807984 := by decide +kernel

theorem rows22250R_4254 : rowsJ2 162 163 60 62 ≤ 10474057526604 := by decide +kernel

theorem rows22250R_4255 : rowsJ2 162 163 62 121 ≤ 702507240831871 := by decide +kernel

theorem rows22250R_4256 : rowsJ2 162 163 121 340 ≤ 1944530990864681 := by decide +kernel

theorem rows22250R_4257 : rowsJ2 163 164 0 40 ≤ 14888012614497 := by decide +kernel

theorem rows22250R_4258 : rowsJ2 163 164 40 42 ≤ 11942961896607 := by decide +kernel

theorem rows22250R_4259 : rowsJ2 163 164 42 44 ≤ 16348582322616 := by decide +kernel

theorem rows22250R_4260 : rowsJ2 163 164 44 45 ≤ 9993627368623 := by decide +kernel

theorem rows22250R_4261 : rowsJ2 163 164 45 46 ≤ 11290033628339 := by decide +kernel

theorem rows22250R_4262 : rowsJ2 163 164 46 47 ≤ 12645992336814 := by decide +kernel

theorem rows22250R_4263 : rowsJ2 163 164 47 48 ≤ 14059328907819 := by decide +kernel

theorem rows22250R_4264 : rowsJ2 163 164 48 49 ≤ 15528097659446 := by decide +kernel

theorem rows22250R_4265 : rowsJ2 163 164 49 50 ≤ 17050570525968 := by decide +kernel

theorem rows22250R_4266 : rowsJ2 163 164 50 51 ≤ 18625227073803 := by decide +kernel

theorem rows22250R_4267 : rowsJ2 163 164 51 52 ≤ 18435236058065 := by decide +kernel

theorem rows22250R_4268 : rowsJ2 163 164 52 53 ≤ 16534054289343 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4253
#print axioms SieveCert.rows22250R_4268
