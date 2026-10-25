/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 180–195 of 5796

File 12 of 465: the parts `rows22250R_180` … `rows22250R_195` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97663 tests: row 34 columns 0–13, row 34 columns 14–16, row 34 columns
17–18, row 34 columns 19–20, row 34 columns 21–21, row 34 columns 22–22, row 34 columns 23–23, row 34 columns 24–24,
row 34 columns 25–25, row 34 columns 26–26, row 34 columns 27–27, row 34 columns 28–28, row 34 columns 29–29, row 34
columns 30–30, row 34 columns 31–31, row 34 columns 32–32), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_180 : rowsJ2 34 35 0 14 ≤ 413062570492 := by decide +kernel

theorem rows22250R_181 : rowsJ2 34 35 14 17 ≤ 1214909800474 := by decide +kernel

theorem rows22250R_182 : rowsJ2 34 35 17 19 ≤ 1565422467602 := by decide +kernel

theorem rows22250R_183 : rowsJ2 34 35 19 21 ≤ 2005902940421 := by decide +kernel

theorem rows22250R_184 : rowsJ2 34 35 21 22 ≤ 1077017101313 := by decide +kernel

theorem rows22250R_185 : rowsJ2 34 35 22 23 ≤ 1104660552489 := by decide +kernel

theorem rows22250R_186 : rowsJ2 34 35 23 24 ≤ 1110996186566 := by decide +kernel

theorem rows22250R_187 : rowsJ2 34 35 24 25 ≤ 1091728595014 := by decide +kernel

theorem rows22250R_188 : rowsJ2 34 35 25 26 ≤ 1047441832366 := by decide +kernel

theorem rows22250R_189 : rowsJ2 34 35 26 27 ≤ 997700037677 := by decide +kernel

theorem rows22250R_190 : rowsJ2 34 35 27 28 ≤ 937836405121 := by decide +kernel

theorem rows22250R_191 : rowsJ2 34 35 28 29 ≤ 873686070185 := by decide +kernel

theorem rows22250R_192 : rowsJ2 34 35 29 30 ≤ 804257007853 := by decide +kernel

theorem rows22250R_193 : rowsJ2 34 35 30 31 ≤ 745021106060 := by decide +kernel

theorem rows22250R_194 : rowsJ2 34 35 31 32 ≤ 694863890408 := by decide +kernel

theorem rows22250R_195 : rowsJ2 34 35 32 33 ≤ 665877585313 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_180
#print axioms SieveCert.rows22250R_195
