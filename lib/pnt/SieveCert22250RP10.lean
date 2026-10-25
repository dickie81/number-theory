/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 148–164 of 5796

File 10 of 465: the parts `rows22250R_148` … `rows22250R_164` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99843 tests: row 32 columns 17–18, row 32 columns 19–19, row 32 columns
20–20, row 32 columns 21–21, row 32 columns 22–22, row 32 columns 23–23, row 32 columns 24–24, row 32 columns 25–25,
row 32 columns 26–26, row 32 columns 27–27, row 32 columns 28–28, row 32 columns 29–29, row 32 columns 30–30, row 32
columns 31–31, row 32 columns 32–359, row 33 columns 0–13, row 33 columns 14–16), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_148 : rowsJ2 32 33 17 19 ≤ 1513991131734 := by decide +kernel

theorem rows22250R_149 : rowsJ2 32 33 19 20 ≤ 970721778701 := by decide +kernel

theorem rows22250R_150 : rowsJ2 32 33 20 21 ≤ 1080846168971 := by decide +kernel

theorem rows22250R_151 : rowsJ2 32 33 21 22 ≤ 1144614623660 := by decide +kernel

theorem rows22250R_152 : rowsJ2 32 33 22 23 ≤ 1179514381094 := by decide +kernel

theorem rows22250R_153 : rowsJ2 32 33 23 24 ≤ 1196033050476 := by decide +kernel

theorem rows22250R_154 : rowsJ2 32 33 24 25 ≤ 1201239127855 := by decide +kernel

theorem rows22250R_155 : rowsJ2 32 33 25 26 ≤ 1176222979205 := by decide +kernel

theorem rows22250R_156 : rowsJ2 32 33 26 27 ≤ 1131085542804 := by decide +kernel

theorem rows22250R_157 : rowsJ2 32 33 27 28 ≤ 1075789569678 := by decide +kernel

theorem rows22250R_158 : rowsJ2 32 33 28 29 ≤ 1015680089729 := by decide +kernel

theorem rows22250R_159 : rowsJ2 32 33 29 30 ≤ 947563808573 := by decide +kernel

theorem rows22250R_160 : rowsJ2 32 33 30 31 ≤ 879470991148 := by decide +kernel

theorem rows22250R_161 : rowsJ2 32 33 31 32 ≤ 818940827937 := by decide +kernel

theorem rows22250R_162 : rowsJ2 32 33 32 360 ≤ 773872950238 := by decide +kernel

theorem rows22250R_163 : rowsJ2 33 34 0 14 ≤ 435410105120 := by decide +kernel

theorem rows22250R_164 : rowsJ2 33 34 14 17 ≤ 1137137051008 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_148
#print axioms SieveCert.rows22250R_164
