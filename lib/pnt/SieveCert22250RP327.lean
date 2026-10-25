/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3865–3880 of 5796

File 327 of 465: the parts `rows22250R_3865` … `rows22250R_3880` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94867 tests: row 125 columns 65–66, row 125 columns 67–67, row 125 columns
68–68, row 125 columns 69–69, row 125 columns 70–70, row 125 columns 71–71, row 125 columns 72–72, row 125 columns
73–74, row 125 columns 75–76, row 125 columns 77–79, row 125 columns 80–82, row 125 columns 83–85, row 125 columns
86–88, row 125 columns 89–91, row 125 columns 92–93, row 125 columns 94–95), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3865 : rowsJ2 125 126 65 67 ≤ 3674889696866 := by decide +kernel

theorem rows22250R_3866 : rowsJ2 125 126 67 68 ≤ 2065089234140 := by decide +kernel

theorem rows22250R_3867 : rowsJ2 125 126 68 69 ≤ 2155767544852 := by decide +kernel

theorem rows22250R_3868 : rowsJ2 125 126 69 70 ≤ 2185478352443 := by decide +kernel

theorem rows22250R_3869 : rowsJ2 125 126 70 71 ≤ 2172384000922 := by decide +kernel

theorem rows22250R_3870 : rowsJ2 125 126 71 72 ≤ 2096372708103 := by decide +kernel

theorem rows22250R_3871 : rowsJ2 125 126 72 73 ≤ 1975574205476 := by decide +kernel

theorem rows22250R_3872 : rowsJ2 125 126 73 75 ≤ 3345428394210 := by decide +kernel

theorem rows22250R_3873 : rowsJ2 125 126 75 77 ≤ 2156403003823 := by decide +kernel

theorem rows22250R_3874 : rowsJ2 125 126 77 80 ≤ 478111924222 := by decide +kernel

theorem rows22250R_3875 : rowsJ2 125 126 80 83 ≤ 0 := by decide +kernel

theorem rows22250R_3876 : rowsJ2 125 126 83 86 ≤ 0 := by decide +kernel

theorem rows22250R_3877 : rowsJ2 125 126 86 89 ≤ 973884464730 := by decide +kernel

theorem rows22250R_3878 : rowsJ2 125 126 89 92 ≤ 4961465738848 := by decide +kernel

theorem rows22250R_3879 : rowsJ2 125 126 92 94 ≤ 6504924306414 := by decide +kernel

theorem rows22250R_3880 : rowsJ2 125 126 94 96 ≤ 9789817890666 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3865
#print axioms SieveCert.rows22250R_3880
