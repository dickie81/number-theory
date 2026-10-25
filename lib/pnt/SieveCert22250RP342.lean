/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 4101–4115 of 5796

File 342 of 465: the parts `rows22250R_4101` … `rows22250R_4115` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 98778 tests: row 132 columns 82–84, row 132 columns 85–88, row 132 columns
89–91, row 132 columns 92–93, row 132 columns 94–95, row 132 columns 96–359, row 133 columns 0–25, row 133 columns
26–28, row 133 columns 29–31, row 133 columns 32–36, row 133 columns 37–54, row 133 columns 55–59, row 133 columns
60–61, row 133 columns 62–62, row 133 columns 63–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4101 : rowsJ2 132 133 82 85 ≤ 1673547903118 := by decide +kernel

theorem rows22250R_4102 : rowsJ2 132 133 85 89 ≤ 1624320593648 := by decide +kernel

theorem rows22250R_4103 : rowsJ2 132 133 89 92 ≤ 7725892564701 := by decide +kernel

theorem rows22250R_4104 : rowsJ2 132 133 92 94 ≤ 9704149022741 := by decide +kernel

theorem rows22250R_4105 : rowsJ2 132 133 94 96 ≤ 14243482123514 := by decide +kernel

theorem rows22250R_4106 : rowsJ2 132 133 96 360 ≤ 906529806927826 := by decide +kernel

theorem rows22250R_4107 : rowsJ2 133 134 0 26 ≤ 1624815214042 := by decide +kernel

theorem rows22250R_4108 : rowsJ2 133 134 26 29 ≤ 9732492423602 := by decide +kernel

theorem rows22250R_4109 : rowsJ2 133 134 29 32 ≤ 12142825636707 := by decide +kernel

theorem rows22250R_4110 : rowsJ2 133 134 32 37 ≤ 8472633223386 := by decide +kernel

theorem rows22250R_4111 : rowsJ2 133 134 37 55 ≤ 1476115473658 := by decide +kernel

theorem rows22250R_4112 : rowsJ2 133 134 55 60 ≤ 3950418944868 := by decide +kernel

theorem rows22250R_4113 : rowsJ2 133 134 60 62 ≤ 3834270519895 := by decide +kernel

theorem rows22250R_4114 : rowsJ2 133 134 62 63 ≤ 2550730958817 := by decide +kernel

theorem rows22250R_4115 : rowsJ2 133 134 63 64 ≤ 3018699221670 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4101
#print axioms SieveCert.rows22250R_4115
