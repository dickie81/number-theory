/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 173–182 of 4715

File 12 of 351: the parts `rows22250R_173` … `rows22250R_182` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, work 84690 in units of a depth-4 test: row 34 columns 23–24, row 34 columns
25–25, row 34 columns 26–26, row 34 columns 27–27, row 34 columns 28–28, row 34 columns 29–29, row 34 columns 30–30,
row 34 columns 31–31, row 34 columns 32–32, row 34 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_173 : rowsJ2 34 35 23 25 ≤ 2274950008483 := by decide +kernel

theorem rows22250R_174 : rowsJ2 34 35 25 26 ≤ 1029119912533 := by decide +kernel

theorem rows22250R_175 : rowsJ2 34 35 26 27 ≤ 941473306918 := by decide +kernel

theorem rows22250R_176 : rowsJ2 34 35 27 28 ≤ 865443267112 := by decide +kernel

theorem rows22250R_177 : rowsJ2 34 35 28 29 ≤ 796052440287 := by decide +kernel

theorem rows22250R_178 : rowsJ2 34 35 29 30 ≤ 753249073470 := by decide +kernel

theorem rows22250R_179 : rowsJ2 34 35 30 31 ≤ 724379141939 := by decide +kernel

theorem rows22250R_180 : rowsJ2 34 35 31 32 ≤ 728515487817 := by decide +kernel

theorem rows22250R_181 : rowsJ2 34 35 32 33 ≤ 765637631375 := by decide +kernel

theorem rows22250R_182 : rowsJ2 34 35 33 34 ≤ 841103787846 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_173
#print axioms SieveCert.rows22250R_182
