/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4583–4599 of 4715

File 343 of 351: the parts `rows22250R_4583` … `rows22250R_4599` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, work 95335 in units of a depth-4 test: row 183 columns 42–42, row 183
columns 43–43, row 183 columns 44–339, row 184 columns 0–32, row 184 columns 33–34, row 184 columns 35–36, row 184
columns 37–37, row 184 columns 38–38, row 184 columns 39–39, row 184 columns 40–40, row 184 columns 41–41, row 184
columns 42–42, row 184 columns 43–339, row 185 columns 0–31, row 185 columns 32–34, row 185 columns 35–36, row 185
columns 37–37), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4583 : rowsJ2 183 184 42 43 ≤ 25099896213248 := by decide +kernel

theorem rows22250R_4584 : rowsJ2 183 184 43 44 ≤ 22366346833887 := by decide +kernel

theorem rows22250R_4585 : rowsJ2 183 184 44 340 ≤ 3595280916850665 := by decide +kernel

theorem rows22250R_4586 : rowsJ2 184 185 0 33 ≤ 24081680327895 := by decide +kernel

theorem rows22250R_4587 : rowsJ2 184 185 33 35 ≤ 24902362311725 := by decide +kernel

theorem rows22250R_4588 : rowsJ2 184 185 35 37 ≤ 38059748823908 := by decide +kernel

theorem rows22250R_4589 : rowsJ2 184 185 37 38 ≤ 23072916178750 := by decide +kernel

theorem rows22250R_4590 : rowsJ2 184 185 38 39 ≤ 25378879538399 := by decide +kernel

theorem rows22250R_4591 : rowsJ2 184 185 39 40 ≤ 27764912101915 := by decide +kernel

theorem rows22250R_4592 : rowsJ2 184 185 40 41 ≤ 30229390470841 := by decide +kernel

theorem rows22250R_4593 : rowsJ2 184 185 41 42 ≤ 27134121800216 := by decide +kernel

theorem rows22250R_4594 : rowsJ2 184 185 42 43 ≤ 24238667578700 := by decide +kernel

theorem rows22250R_4595 : rowsJ2 184 185 43 340 ≤ 3728522943619045 := by decide +kernel

theorem rows22250R_4596 : rowsJ2 185 186 0 32 ≤ 18454065636750 := by decide +kernel

theorem rows22250R_4597 : rowsJ2 185 186 32 35 ≤ 36651071349851 := by decide +kernel

theorem rows22250R_4598 : rowsJ2 185 186 35 37 ≤ 41122718702202 := by decide +kernel

theorem rows22250R_4599 : rowsJ2 185 186 37 38 ≤ 24810853275616 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4583
#print axioms SieveCert.rows22250R_4599
