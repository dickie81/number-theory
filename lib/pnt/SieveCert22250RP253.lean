/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2779–2785 of 5796

File 253 of 465: the parts `rows22250R_2779` … `rows22250R_2785` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 90104 tests: row 98 columns 87–87, row 98 columns 88–88, row 98 columns
89–89, row 98 columns 90–90, row 98 columns 91–91, row 98 columns 92–92, row 98 columns 93–93), each a sum of
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

theorem rows22250R_2779 : rowsJ2 98 99 87 88 ≤ 2046019792352 := by decide +kernel

theorem rows22250R_2780 : rowsJ2 98 99 88 89 ≤ 2684672760285 := by decide +kernel

theorem rows22250R_2781 : rowsJ2 98 99 89 90 ≤ 3452039717964 := by decide +kernel

theorem rows22250R_2782 : rowsJ2 98 99 90 91 ≤ 4295446858739 := by decide +kernel

theorem rows22250R_2783 : rowsJ2 98 99 91 92 ≤ 4970737219374 := by decide +kernel

theorem rows22250R_2784 : rowsJ2 98 99 92 93 ≤ 4413912674744 := by decide +kernel

theorem rows22250R_2785 : rowsJ2 98 99 93 94 ≤ 3915318802068 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2779
#print axioms SieveCert.rows22250R_2785
