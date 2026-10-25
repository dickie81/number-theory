/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 204–215 of 4715

File 15 of 351: the parts `rows22250R_204` … `rows22250R_215` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99096 tests: row 36 columns 19–20, row 36 columns 21–22, row 36 columns
23–24, row 36 columns 25–25, row 36 columns 26–26, row 36 columns 27–27, row 36 columns 28–28, row 36 columns 29–29,
row 36 columns 30–30, row 36 columns 31–31, row 36 columns 32–32, row 36 columns 33–33), each a sum of refined costs
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

theorem rows22250R_204 : rowsJ2 36 37 19 21 ≤ 2301640381889 := by decide +kernel

theorem rows22250R_205 : rowsJ2 36 37 21 23 ≤ 2197473480557 := by decide +kernel

theorem rows22250R_206 : rowsJ2 36 37 23 25 ≤ 1952715392576 := by decide +kernel

theorem rows22250R_207 : rowsJ2 36 37 25 26 ≤ 862297888854 := by decide +kernel

theorem rows22250R_208 : rowsJ2 36 37 26 27 ≤ 784701503020 := by decide +kernel

theorem rows22250R_209 : rowsJ2 36 37 27 28 ≤ 722566252366 := by decide +kernel

theorem rows22250R_210 : rowsJ2 36 37 28 29 ≤ 670031777842 := by decide +kernel

theorem rows22250R_211 : rowsJ2 36 37 29 30 ≤ 639052511947 := by decide +kernel

theorem rows22250R_212 : rowsJ2 36 37 30 31 ≤ 626690072476 := by decide +kernel

theorem rows22250R_213 : rowsJ2 36 37 31 32 ≤ 652705497829 := by decide +kernel

theorem rows22250R_214 : rowsJ2 36 37 32 33 ≤ 716298838270 := by decide +kernel

theorem rows22250R_215 : rowsJ2 36 37 33 34 ≤ 755300622825 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_204
#print axioms SieveCert.rows22250R_215
