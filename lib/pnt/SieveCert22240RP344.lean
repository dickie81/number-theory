/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4379–4392 of 5066

File 344 of 387: the parts `rows22240R_4379` … `rows22240R_4392` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 95110 in units of a depth-4 test: row 153 columns 69–72, row 153
columns 73–339, row 154 columns 0–41, row 154 columns 42–44, row 154 columns 45–46, row 154 columns 47–48, row 154
columns 49–49, row 154 columns 50–50, row 154 columns 51–51, row 154 columns 52–52, row 154 columns 53–53, row 154
columns 54–54, row 154 columns 55–55, row 154 columns 56–56), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4379 : rowsJ2 153 154 69 73 ≤ 7169949008807 := by decide +kernel

theorem rows22240R_4380 : rowsJ2 153 154 73 340 ≤ 2263871701221735 := by decide +kernel

theorem rows22240R_4381 : rowsJ2 154 155 0 42 ≤ 4488493357038 := by decide +kernel

theorem rows22240R_4382 : rowsJ2 154 155 42 45 ≤ 9116426974534 := by decide +kernel

theorem rows22240R_4383 : rowsJ2 154 155 45 47 ≤ 9969853610578 := by decide +kernel

theorem rows22240R_4384 : rowsJ2 154 155 47 49 ≤ 13667742939371 := by decide +kernel

theorem rows22240R_4385 : rowsJ2 154 155 49 50 ≤ 8363192264993 := by decide +kernel

theorem rows22240R_4386 : rowsJ2 154 155 50 51 ≤ 9454157280457 := by decide +kernel

theorem rows22240R_4387 : rowsJ2 154 155 51 52 ≤ 10596163433157 := by decide +kernel

theorem rows22240R_4388 : rowsJ2 154 155 52 53 ≤ 11787359786485 := by decide +kernel

theorem rows22240R_4389 : rowsJ2 154 155 53 54 ≤ 13026065032974 := by decide +kernel

theorem rows22240R_4390 : rowsJ2 154 155 54 55 ≤ 14310737215811 := by decide +kernel

theorem rows22240R_4391 : rowsJ2 154 155 55 56 ≤ 15639991877072 := by decide +kernel

theorem rows22240R_4392 : rowsJ2 154 155 56 57 ≤ 17012549070178 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4379
#print axioms SieveCert.rows22240R_4392
