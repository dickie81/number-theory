/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4422–4437 of 5066

File 347 of 387: the parts `rows22240R_4422` … `rows22240R_4437` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 95851 in units of a depth-4 test: row 155 columns 62–62, row 155
columns 63–63, row 155 columns 64–65, row 155 columns 66–67, row 155 columns 68–71, row 155 columns 72–339, row 156
columns 0–41, row 156 columns 42–44, row 156 columns 45–46, row 156 columns 47–47, row 156 columns 48–48, row 156
columns 49–49, row 156 columns 50–50, row 156 columns 51–51, row 156 columns 52–52, row 156 columns 53–53), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4422 : rowsJ2 155 156 62 63 ≤ 7969685225857 := by decide +kernel

theorem rows22240R_4423 : rowsJ2 155 156 63 64 ≤ 6878827007042 := by decide +kernel

theorem rows22240R_4424 : rowsJ2 155 156 64 66 ≤ 10826592595246 := by decide +kernel

theorem rows22240R_4425 : rowsJ2 155 156 66 68 ≤ 7470586562047 := by decide +kernel

theorem rows22240R_4426 : rowsJ2 155 156 68 72 ≤ 7421092762042 := by decide +kernel

theorem rows22240R_4427 : rowsJ2 155 156 72 340 ≤ 2493391992334028 := by decide +kernel

theorem rows22240R_4428 : rowsJ2 156 157 0 42 ≤ 6990366916077 := by decide +kernel

theorem rows22240R_4429 : rowsJ2 156 157 42 45 ≤ 11746384252264 := by decide +kernel

theorem rows22240R_4430 : rowsJ2 156 157 45 47 ≤ 12199143628769 := by decide +kernel

theorem rows22240R_4431 : rowsJ2 156 157 47 48 ≤ 7597218078804 := by decide +kernel

theorem rows22240R_4432 : rowsJ2 156 157 48 49 ≤ 8672454003880 := by decide +kernel

theorem rows22240R_4433 : rowsJ2 156 157 49 50 ≤ 9802379998760 := by decide +kernel

theorem rows22240R_4434 : rowsJ2 156 157 50 51 ≤ 10984969306530 := by decide +kernel

theorem rows22240R_4435 : rowsJ2 156 157 51 52 ≤ 12218327816425 := by decide +kernel

theorem rows22240R_4436 : rowsJ2 156 157 52 53 ≤ 13500734248914 := by decide +kernel

theorem rows22240R_4437 : rowsJ2 156 157 53 54 ≤ 14830615408807 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4422
#print axioms SieveCert.rows22240R_4437
