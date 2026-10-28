/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3632–3644 of 4715

File 279 of 351: the parts `rows22250R_3632` … `rows22250R_3644` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 98690 in units of a depth-4 test: row 136 columns 61–61, row 136
columns 62–62, row 136 columns 63–63, row 136 columns 64–64, row 136 columns 65–65, row 136 columns 66–66, row 136
columns 67–67, row 136 columns 68–68, row 136 columns 69–69, row 136 columns 70–70, row 136 columns 71–71, row 136
columns 72–72, row 136 columns 73–73), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3632 : rowsJ2 136 137 61 62 ≤ 9169071964349 := by decide +kernel

theorem rows22250R_3633 : rowsJ2 136 137 62 63 ≤ 9916146103810 := by decide +kernel

theorem rows22250R_3634 : rowsJ2 136 137 63 64 ≤ 10616679922686 := by decide +kernel

theorem rows22250R_3635 : rowsJ2 136 137 64 65 ≤ 11248839624017 := by decide +kernel

theorem rows22250R_3636 : rowsJ2 136 137 65 66 ≤ 10162104884126 := by decide +kernel

theorem rows22250R_3637 : rowsJ2 136 137 66 67 ≤ 9128573486909 := by decide +kernel

theorem rows22250R_3638 : rowsJ2 136 137 67 68 ≤ 8168066903791 := by decide +kernel

theorem rows22250R_3639 : rowsJ2 136 137 68 69 ≤ 7256796618190 := by decide +kernel

theorem rows22250R_3640 : rowsJ2 136 137 69 70 ≤ 6415042100524 := by decide +kernel

theorem rows22250R_3641 : rowsJ2 136 137 70 71 ≤ 5618956840144 := by decide +kernel

theorem rows22250R_3642 : rowsJ2 136 137 71 72 ≤ 4889272953656 := by decide +kernel

theorem rows22250R_3643 : rowsJ2 136 137 72 73 ≤ 4202050025492 := by decide +kernel

theorem rows22250R_3644 : rowsJ2 136 137 73 74 ≤ 3578470741416 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3632
#print axioms SieveCert.rows22250R_3644
