/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4747–4758 of 5796

File 392 of 465: the parts `rows22250R_4747` … `rows22250R_4758` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99985 tests: row 153 columns 63–63, row 153 columns 64–64, row 153 columns
65–65, row 153 columns 66–66, row 153 columns 67–67, row 153 columns 68–68, row 153 columns 69–69, row 153 columns
70–70, row 153 columns 71–71, row 153 columns 72–72, row 153 columns 73–73, row 153 columns 74–74), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4747 : rowsJ2 153 154 63 64 ≤ 12340351468948 := by decide +kernel

theorem rows22250R_4748 : rowsJ2 153 154 64 65 ≤ 12231911330542 := by decide +kernel

theorem rows22250R_4749 : rowsJ2 153 154 65 66 ≤ 11063195606356 := by decide +kernel

theorem rows22250R_4750 : rowsJ2 153 154 66 67 ≤ 9960946676761 := by decide +kernel

theorem rows22250R_4751 : rowsJ2 153 154 67 68 ≤ 8923492335570 := by decide +kernel

theorem rows22250R_4752 : rowsJ2 153 154 68 69 ≤ 7949269671159 := by decide +kernel

theorem rows22250R_4753 : rowsJ2 153 154 69 70 ≤ 7036820345268 := by decide +kernel

theorem rows22250R_4754 : rowsJ2 153 154 70 71 ≤ 6184786268400 := by decide +kernel

theorem rows22250R_4755 : rowsJ2 153 154 71 72 ≤ 5391905646547 := by decide +kernel

theorem rows22250R_4756 : rowsJ2 153 154 72 73 ≤ 4657009376855 := by decide +kernel

theorem rows22250R_4757 : rowsJ2 153 154 73 74 ≤ 3979017771912 := by decide +kernel

theorem rows22250R_4758 : rowsJ2 153 154 74 75 ≤ 3356937594864 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4747
#print axioms SieveCert.rows22250R_4758
