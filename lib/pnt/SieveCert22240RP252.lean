/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3050–3065 of 5066

File 252 of 387: the parts `rows22240R_3050` … `rows22240R_3065` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96767 in units of a depth-4 test: row 106 columns 83–84, row 106
columns 85–86, row 106 columns 87–88, row 106 columns 89–90, row 106 columns 91–92, row 106 columns 93–93, row 106
columns 94–94, row 106 columns 95–95, row 106 columns 96–96, row 106 columns 97–97, row 106 columns 98–98, row 106
columns 99–99, row 106 columns 100–100, row 106 columns 101–339, row 107 columns 0–20, row 107 columns 21–30), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3050 : rowsJ2 106 107 83 85 ≤ 1612578418841 := by decide +kernel

theorem rows22240R_3051 : rowsJ2 106 107 85 87 ≤ 2307980068468 := by decide +kernel

theorem rows22240R_3052 : rowsJ2 106 107 87 89 ≤ 3598910921376 := by decide +kernel

theorem rows22240R_3053 : rowsJ2 106 107 89 91 ≤ 5511361293825 := by decide +kernel

theorem rows22240R_3054 : rowsJ2 106 107 91 93 ≤ 8076260671652 := by decide +kernel

theorem rows22240R_3055 : rowsJ2 106 107 93 94 ≤ 5217581675320 := by decide +kernel

theorem rows22240R_3056 : rowsJ2 106 107 94 95 ≤ 6111497593866 := by decide +kernel

theorem rows22240R_3057 : rowsJ2 106 107 95 96 ≤ 7114532081364 := by decide +kernel

theorem rows22240R_3058 : rowsJ2 106 107 96 97 ≤ 8195815522347 := by decide +kernel

theorem rows22240R_3059 : rowsJ2 106 107 97 98 ≤ 9392660303674 := by decide +kernel

theorem rows22240R_3060 : rowsJ2 106 107 98 99 ≤ 10657020820370 := by decide +kernel

theorem rows22240R_3061 : rowsJ2 106 107 99 100 ≤ 12043783131993 := by decide +kernel

theorem rows22240R_3062 : rowsJ2 106 107 100 101 ≤ 13504016270718 := by decide +kernel

theorem rows22240R_3063 : rowsJ2 106 107 101 340 ≤ 606770241313259 := by decide +kernel

theorem rows22240R_3064 : rowsJ2 107 108 0 21 ≤ 0 := by decide +kernel

theorem rows22240R_3065 : rowsJ2 107 108 21 31 ≤ 4076170506128 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3050
#print axioms SieveCert.rows22240R_3065
