/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3946–3962 of 5796

File 332 of 465: the parts `rows22250R_3946` … `rows22250R_3962` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98028 tests: row 127 columns 99–99, row 127 columns 100–359, row 128 columns
0–26, row 128 columns 27–29, row 128 columns 30–31, row 128 columns 32–33, row 128 columns 34–36, row 128 columns
37–41, row 128 columns 42–56, row 128 columns 57–61, row 128 columns 62–63, row 128 columns 64–64, row 128 columns
65–65, row 128 columns 66–66, row 128 columns 67–67, row 128 columns 68–68, row 128 columns 69–69), each a sum of
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

theorem rows22250R_3946 : rowsJ2 127 128 99 100 ≤ 10852051870425 := by decide +kernel

theorem rows22250R_3947 : rowsJ2 127 128 100 360 ≤ 1094524525062338 := by decide +kernel

theorem rows22250R_3948 : rowsJ2 128 129 0 27 ≤ 1070226430466 := by decide +kernel

theorem rows22250R_3949 : rowsJ2 128 129 27 30 ≤ 8248786357096 := by decide +kernel

theorem rows22250R_3950 : rowsJ2 128 129 30 32 ≤ 12298400592510 := by decide +kernel

theorem rows22250R_3951 : rowsJ2 128 129 32 34 ≤ 11577294230855 := by decide +kernel

theorem rows22250R_3952 : rowsJ2 128 129 34 37 ≤ 11747065130104 := by decide +kernel

theorem rows22250R_3953 : rowsJ2 128 129 37 42 ≤ 7394095421704 := by decide +kernel

theorem rows22250R_3954 : rowsJ2 128 129 42 57 ≤ 220108397344 := by decide +kernel

theorem rows22250R_3955 : rowsJ2 128 129 57 62 ≤ 3138575420899 := by decide +kernel

theorem rows22250R_3956 : rowsJ2 128 129 62 64 ≤ 3235559751279 := by decide +kernel

theorem rows22250R_3957 : rowsJ2 128 129 64 65 ≤ 2150491973385 := by decide +kernel

theorem rows22250R_3958 : rowsJ2 128 129 65 66 ≤ 2447174443233 := by decide +kernel

theorem rows22250R_3959 : rowsJ2 128 129 66 67 ≤ 2704131743365 := by decide +kernel

theorem rows22250R_3960 : rowsJ2 128 129 67 68 ≤ 2902409504206 := by decide +kernel

theorem rows22250R_3961 : rowsJ2 128 129 68 69 ≤ 3059924173691 := by decide +kernel

theorem rows22250R_3962 : rowsJ2 128 129 69 70 ≤ 3157348993280 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3946
#print axioms SieveCert.rows22250R_3962
