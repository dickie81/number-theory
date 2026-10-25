/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3625–3638 of 5796

File 311 of 465: the parts `rows22250R_3625` … `rows22250R_3638` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97632 tests: row 117 columns 41–42, row 117 columns 43–44, row 117 columns
45–47, row 117 columns 48–52, row 117 columns 53–63, row 117 columns 64–68, row 117 columns 69–73, row 117 columns
74–77, row 117 columns 78–80, row 117 columns 81–82, row 117 columns 83–84, row 117 columns 85–87, row 117 columns
88–90, row 117 columns 91–92), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3625 : rowsJ2 117 118 41 43 ≤ 11278023173950 := by decide +kernel

theorem rows22250R_3626 : rowsJ2 117 118 43 45 ≤ 7313787554900 := by decide +kernel

theorem rows22250R_3627 : rowsJ2 117 118 45 48 ≤ 5034051667140 := by decide +kernel

theorem rows22250R_3628 : rowsJ2 117 118 48 53 ≤ 657738740806 := by decide +kernel

theorem rows22250R_3629 : rowsJ2 117 118 53 64 ≤ 421362615635 := by decide +kernel

theorem rows22250R_3630 : rowsJ2 117 118 64 69 ≤ 2020732253469 := by decide +kernel

theorem rows22250R_3631 : rowsJ2 117 118 69 74 ≤ 189858401880 := by decide +kernel

theorem rows22250R_3632 : rowsJ2 117 118 74 78 ≤ 0 := by decide +kernel

theorem rows22250R_3633 : rowsJ2 117 118 78 81 ≤ 46126977450 := by decide +kernel

theorem rows22250R_3634 : rowsJ2 117 118 81 83 ≤ 319904934942 := by decide +kernel

theorem rows22250R_3635 : rowsJ2 117 118 83 85 ≤ 243907700595 := by decide +kernel

theorem rows22250R_3636 : rowsJ2 117 118 85 88 ≤ 253295371719 := by decide +kernel

theorem rows22250R_3637 : rowsJ2 117 118 88 91 ≤ 1671613643963 := by decide +kernel

theorem rows22250R_3638 : rowsJ2 117 118 91 93 ≤ 2791969196048 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3625
#print axioms SieveCert.rows22250R_3638
