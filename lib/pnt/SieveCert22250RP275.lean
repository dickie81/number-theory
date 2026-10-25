/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3576–3588 of 4715

File 275 of 351: the parts `rows22250R_3576` … `rows22250R_3588` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 98606 tests: row 134 columns 61–61, row 134 columns 62–62, row 134 columns
63–63, row 134 columns 64–64, row 134 columns 65–65, row 134 columns 66–66, row 134 columns 67–67, row 134 columns
68–68, row 134 columns 69–69, row 134 columns 70–70, row 134 columns 71–71, row 134 columns 72–72, row 134 columns
73–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3576 : rowsJ2 134 135 61 62 ≤ 7999315558386 := by decide +kernel

theorem rows22250R_3577 : rowsJ2 134 135 62 63 ≤ 8681522714674 := by decide +kernel

theorem rows22250R_3578 : rowsJ2 134 135 63 64 ≤ 9316488073416 := by decide +kernel

theorem rows22250R_3579 : rowsJ2 134 135 64 65 ≤ 9882075491269 := by decide +kernel

theorem rows22250R_3580 : rowsJ2 134 135 65 66 ≤ 10399515380213 := by decide +kernel

theorem rows22250R_3581 : rowsJ2 134 135 66 67 ≤ 9367444419639 := by decide +kernel

theorem rows22250R_3582 : rowsJ2 134 135 67 68 ≤ 8408472062515 := by decide +kernel

theorem rows22250R_3583 : rowsJ2 134 135 68 69 ≤ 7498565853566 := by decide +kernel

theorem rows22250R_3584 : rowsJ2 134 135 69 70 ≤ 6658246943294 := by decide +kernel

theorem rows22250R_3585 : rowsJ2 134 135 70 71 ≤ 5863421827207 := by decide +kernel

theorem rows22250R_3586 : rowsJ2 134 135 71 72 ≤ 5135066989988 := by decide +kernel

theorem rows22250R_3587 : rowsJ2 134 135 72 73 ≤ 4448991765068 := by decide +kernel

theorem rows22250R_3588 : rowsJ2 134 135 73 74 ≤ 3826626049482 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3576
#print axioms SieveCert.rows22250R_3588
