/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3819–3834 of 5796

File 324 of 465: the parts `rows22250R_3819` … `rows22250R_3834` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99492 tests: row 123 columns 92–93, row 123 columns 94–95, row 123 columns
96–97, row 123 columns 98–98, row 123 columns 99–99, row 123 columns 100–100, row 123 columns 101–101, row 123
columns 102–359, row 124 columns 0–26, row 124 columns 27–30, row 124 columns 31–32, row 124 columns 33–34, row 124
columns 35–36, row 124 columns 37–39, row 124 columns 40–43, row 124 columns 44–52), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3819 : rowsJ2 123 124 92 94 ≤ 5731716555700 := by decide +kernel

theorem rows22250R_3820 : rowsJ2 123 124 94 96 ≤ 8715103509197 := by decide +kernel

theorem rows22250R_3821 : rowsJ2 123 124 96 98 ≤ 12332146352083 := by decide +kernel

theorem rows22250R_3822 : rowsJ2 123 124 98 99 ≤ 7737352071971 := by decide +kernel

theorem rows22250R_3823 : rowsJ2 123 124 99 100 ≤ 8887134634249 := by decide +kernel

theorem rows22250R_3824 : rowsJ2 123 124 100 101 ≤ 10151584291628 := by decide +kernel

theorem rows22250R_3825 : rowsJ2 123 124 101 102 ≤ 11488359397159 := by decide +kernel

theorem rows22250R_3826 : rowsJ2 123 124 102 360 ≤ 1298096454276797 := by decide +kernel

theorem rows22250R_3827 : rowsJ2 124 125 0 27 ≤ 584096734118 := by decide +kernel

theorem rows22250R_3828 : rowsJ2 124 125 27 31 ≤ 8656593875980 := by decide +kernel

theorem rows22250R_3829 : rowsJ2 124 125 31 33 ≤ 11742365503889 := by decide +kernel

theorem rows22250R_3830 : rowsJ2 124 125 33 35 ≤ 16144311504198 := by decide +kernel

theorem rows22250R_3831 : rowsJ2 124 125 35 37 ≤ 12854848909333 := by decide +kernel

theorem rows22250R_3832 : rowsJ2 124 125 37 40 ≤ 13623264713760 := by decide +kernel

theorem rows22250R_3833 : rowsJ2 124 125 40 44 ≤ 7143334146820 := by decide +kernel

theorem rows22250R_3834 : rowsJ2 124 125 44 53 ≤ 936055164694 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3819
#print axioms SieveCert.rows22250R_3834
