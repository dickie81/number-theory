/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 5022–5037 of 5066

File 385 of 387: the parts `rows22240R_5022` … `rows22240R_5037` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 98355 in units of a depth-4 test: rows 204–204, rows 205–205, rows
206–206, rows 207–207, rows 208–209, rows 210–211, rows 212–213, rows 214–215, rows 216–217, rows 218–219, rows
220–221, rows 222–223, rows 224–225, rows 226–227, rows 228–229, rows 230–231), each a sum of refined costs (`rows2`
or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_5022 : rows2 204 205 ≤ 6193270552706890 := by decide +kernel

theorem rows22240R_5023 : rows2 205 206 ≤ 6318066050966561 := by decide +kernel

theorem rows22240R_5024 : rows2 206 207 ≤ 6446066570448579 := by decide +kernel

theorem rows22240R_5025 : rows2 207 208 ≤ 6577130056619976 := by decide +kernel

theorem rows22240R_5026 : rows2 208 210 ≤ 13559632279955690 := by decide +kernel

theorem rows22240R_5027 : rows2 210 212 ≤ 14119408258486945 := by decide +kernel

theorem rows22240R_5028 : rows2 212 214 ≤ 14439316054514144 := by decide +kernel

theorem rows22240R_5029 : rows2 214 216 ≤ 14728644480909049 := by decide +kernel

theorem rows22240R_5030 : rows2 216 218 ≤ 15040343208552094 := by decide +kernel

theorem rows22240R_5031 : rows2 218 220 ≤ 15375479799804811 := by decide +kernel

theorem rows22240R_5032 : rows2 220 222 ≤ 15735088742772712 := by decide +kernel

theorem rows22240R_5033 : rows2 222 224 ≤ 16119709407938834 := by decide +kernel

theorem rows22240R_5034 : rows2 224 226 ≤ 16523379768036017 := by decide +kernel

theorem rows22240R_5035 : rows2 226 228 ≤ 16943852691111159 := by decide +kernel

theorem rows22240R_5036 : rows2 228 230 ≤ 17382381386273937 := by decide +kernel

theorem rows22240R_5037 : rows2 230 232 ≤ 17840474741396672 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_5022
#print axioms SieveCert.rows22240R_5037
