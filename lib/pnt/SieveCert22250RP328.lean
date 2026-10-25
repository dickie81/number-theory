/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3881–3895 of 5796

File 328 of 465: the parts `rows22250R_3881` … `rows22250R_3895` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98420 tests: row 125 columns 96–97, row 125 columns 98–99, row 125 columns
100–100, row 125 columns 101–359, row 126 columns 0–26, row 126 columns 27–29, row 126 columns 30–31, row 126
columns 32–33, row 126 columns 34–35, row 126 columns 36–38, row 126 columns 39–43, row 126 columns 44–57, row 126
columns 58–62, row 126 columns 63–64, row 126 columns 65–66), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3881 : rowsJ2 125 126 96 98 ≤ 13744986990798 := by decide +kernel

theorem rows22250R_3882 : rowsJ2 125 126 98 100 ≤ 18416816524752 := by decide +kernel

theorem rows22250R_3883 : rowsJ2 125 126 100 101 ≤ 11204635426699 := by decide +kernel

theorem rows22250R_3884 : rowsJ2 125 126 101 360 ≤ 1194882973134172 := by decide +kernel

theorem rows22250R_3885 : rowsJ2 126 127 0 27 ≤ 879288740080 := by decide +kernel

theorem rows22250R_3886 : rowsJ2 126 127 27 30 ≤ 6208046100216 := by decide +kernel

theorem rows22250R_3887 : rowsJ2 126 127 30 32 ≤ 10493906886329 := by decide +kernel

theorem rows22250R_3888 : rowsJ2 126 127 32 34 ≤ 14655159778834 := by decide +kernel

theorem rows22250R_3889 : rowsJ2 126 127 34 36 ≤ 11431088816435 := by decide +kernel

theorem rows22250R_3890 : rowsJ2 126 127 36 39 ≤ 11606548226395 := by decide +kernel

theorem rows22250R_3891 : rowsJ2 126 127 39 44 ≤ 6106500539818 := by decide +kernel

theorem rows22250R_3892 : rowsJ2 126 127 44 58 ≤ 215888932207 := by decide +kernel

theorem rows22250R_3893 : rowsJ2 126 127 58 63 ≤ 3057981994156 := by decide +kernel

theorem rows22250R_3894 : rowsJ2 126 127 63 65 ≤ 3116868432803 := by decide +kernel

theorem rows22250R_3895 : rowsJ2 126 127 65 67 ≤ 4147264729859 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3881
#print axioms SieveCert.rows22250R_3895
