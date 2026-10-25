/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3929–3945 of 5796

File 331 of 465: the parts `rows22250R_3929` … `rows22250R_3945` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 99059 tests: row 127 columns 69–69, row 127 columns 70–70, row 127 columns
71–71, row 127 columns 72–72, row 127 columns 73–73, row 127 columns 74–74, row 127 columns 75–75, row 127 columns
76–76, row 127 columns 77–78, row 127 columns 79–81, row 127 columns 82–84, row 127 columns 85–87, row 127 columns
88–90, row 127 columns 91–92, row 127 columns 93–94, row 127 columns 95–96, row 127 columns 97–98), each a sum of
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

theorem rows22250R_3929 : rowsJ2 127 128 69 70 ≤ 2815473365552 := by decide +kernel

theorem rows22250R_3930 : rowsJ2 127 128 70 71 ≤ 2847799186343 := by decide +kernel

theorem rows22250R_3931 : rowsJ2 127 128 71 72 ≤ 2817865175320 := by decide +kernel

theorem rows22250R_3932 : rowsJ2 127 128 72 73 ≤ 2743622942025 := by decide +kernel

theorem rows22250R_3933 : rowsJ2 127 128 73 74 ≤ 2604768707853 := by decide +kernel

theorem rows22250R_3934 : rowsJ2 127 128 74 75 ≤ 2419203720168 := by decide +kernel

theorem rows22250R_3935 : rowsJ2 127 128 75 76 ≤ 2166131261871 := by decide +kernel

theorem rows22250R_3936 : rowsJ2 127 128 76 77 ≤ 1863376009101 := by decide +kernel

theorem rows22250R_3937 : rowsJ2 127 128 77 79 ≤ 2315162429949 := by decide +kernel

theorem rows22250R_3938 : rowsJ2 127 128 79 82 ≤ 427731345023 := by decide +kernel

theorem rows22250R_3939 : rowsJ2 127 128 82 85 ≤ 0 := by decide +kernel

theorem rows22250R_3940 : rowsJ2 127 128 85 88 ≤ 348802441288 := by decide +kernel

theorem rows22250R_3941 : rowsJ2 127 128 88 91 ≤ 3944654136107 := by decide +kernel

theorem rows22250R_3942 : rowsJ2 127 128 91 93 ≤ 5780776223636 := by decide +kernel

theorem rows22250R_3943 : rowsJ2 127 128 93 95 ≤ 9052215703125 := by decide +kernel

theorem rows22250R_3944 : rowsJ2 127 128 95 97 ≤ 13011074904304 := by decide +kernel

theorem rows22250R_3945 : rowsJ2 127 128 97 99 ≤ 17705587031298 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3929
#print axioms SieveCert.rows22250R_3945
