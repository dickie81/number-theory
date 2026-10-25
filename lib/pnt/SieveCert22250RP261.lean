/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2876–2883 of 5796

File 261 of 465: the parts `rows22250R_2876` … `rows22250R_2883` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 95891 tests: row 100 columns 89–89, row 100 columns 90–90, row 100 columns
91–91, row 100 columns 92–92, row 100 columns 93–93, row 100 columns 94–94, row 100 columns 95–95, row 100 columns
96–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2876 : rowsJ2 100 101 89 90 ≤ 3358355782203 := by decide +kernel

theorem rows22250R_2877 : rowsJ2 100 101 90 91 ≤ 3895660351011 := by decide +kernel

theorem rows22250R_2878 : rowsJ2 100 101 91 92 ≤ 3409881423973 := by decide +kernel

theorem rows22250R_2879 : rowsJ2 100 101 92 93 ≤ 3233615394568 := by decide +kernel

theorem rows22250R_2880 : rowsJ2 100 101 93 94 ≤ 3083798940115 := by decide +kernel

theorem rows22250R_2881 : rowsJ2 100 101 94 95 ≤ 3005707301136 := by decide +kernel

theorem rows22250R_2882 : rowsJ2 100 101 95 96 ≤ 2985764025810 := by decide +kernel

theorem rows22250R_2883 : rowsJ2 100 101 96 97 ≤ 3039295155698 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2876
#print axioms SieveCert.rows22250R_2883
