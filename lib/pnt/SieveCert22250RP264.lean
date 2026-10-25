/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2913–2924 of 5796

File 264 of 465: the parts `rows22250R_2913` … `rows22250R_2924` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 90834 tests: row 101 columns 61–63, row 101 columns 64–68, row 101 columns
69–74, row 101 columns 75–78, row 101 columns 79–81, row 101 columns 82–83, row 101 columns 84–84, row 101 columns
85–85, row 101 columns 86–86, row 101 columns 87–87, row 101 columns 88–88, row 101 columns 89–89), each a sum of
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

theorem rows22250R_2913 : rowsJ2 101 102 61 64 ≤ 0 := by decide +kernel

theorem rows22250R_2914 : rowsJ2 101 102 64 69 ≤ 0 := by decide +kernel

theorem rows22250R_2915 : rowsJ2 101 102 69 75 ≤ 0 := by decide +kernel

theorem rows22250R_2916 : rowsJ2 101 102 75 79 ≤ 0 := by decide +kernel

theorem rows22250R_2917 : rowsJ2 101 102 79 82 ≤ 203456942201 := by decide +kernel

theorem rows22250R_2918 : rowsJ2 101 102 82 84 ≤ 846887297986 := by decide +kernel

theorem rows22250R_2919 : rowsJ2 101 102 84 85 ≤ 804873194891 := by decide +kernel

theorem rows22250R_2920 : rowsJ2 101 102 85 86 ≤ 1127560454829 := by decide +kernel

theorem rows22250R_2921 : rowsJ2 101 102 86 87 ≤ 1509528497104 := by decide +kernel

theorem rows22250R_2922 : rowsJ2 101 102 87 88 ≤ 2009948610122 := by decide +kernel

theorem rows22250R_2923 : rowsJ2 101 102 88 89 ≤ 2651289436135 := by decide +kernel

theorem rows22250R_2924 : rowsJ2 101 102 89 90 ≤ 3194513202879 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2913
#print axioms SieveCert.rows22250R_2924
