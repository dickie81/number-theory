/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3041–3056 of 5796

File 274 of 465: the parts `rows22250R_3041` … `rows22250R_3056` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 95555 tests: row 104 columns 39–39, row 104 columns 40–40, row 104 columns
41–41, row 104 columns 42–42, row 104 columns 43–43, row 104 columns 44–44, row 104 columns 45–45, row 104 columns
46–46, row 104 columns 47–47, row 104 columns 48–48, row 104 columns 49–49, row 104 columns 50–50, row 104 columns
51–51, row 104 columns 52–53, row 104 columns 54–55, row 104 columns 56–57), each a sum of refined costs (`rows2` or
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

theorem rows22250R_3041 : rowsJ2 104 105 39 40 ≤ 9081695353585 := by decide +kernel

theorem rows22250R_3042 : rowsJ2 104 105 40 41 ≤ 10432244589626 := by decide +kernel

theorem rows22250R_3043 : rowsJ2 104 105 41 42 ≤ 11788555196442 := by decide +kernel

theorem rows22250R_3044 : rowsJ2 104 105 42 43 ≤ 13148585736743 := by decide +kernel

theorem rows22250R_3045 : rowsJ2 104 105 43 44 ≤ 14317644561584 := by decide +kernel

theorem rows22250R_3046 : rowsJ2 104 105 44 45 ≤ 12771015509604 := by decide +kernel

theorem rows22250R_3047 : rowsJ2 104 105 45 46 ≤ 11241985295958 := by decide +kernel

theorem rows22250R_3048 : rowsJ2 104 105 46 47 ≤ 9778859530530 := by decide +kernel

theorem rows22250R_3049 : rowsJ2 104 105 47 48 ≤ 8331132274264 := by decide +kernel

theorem rows22250R_3050 : rowsJ2 104 105 48 49 ≤ 7030261377097 := by decide +kernel

theorem rows22250R_3051 : rowsJ2 104 105 49 50 ≤ 5873245653691 := by decide +kernel

theorem rows22250R_3052 : rowsJ2 104 105 50 51 ≤ 4857389165942 := by decide +kernel

theorem rows22250R_3053 : rowsJ2 104 105 51 52 ≤ 3980291165493 := by decide +kernel

theorem rows22250R_3054 : rowsJ2 104 105 52 54 ≤ 5579627284338 := by decide +kernel

theorem rows22250R_3055 : rowsJ2 104 105 54 56 ≤ 2828434515005 := by decide +kernel

theorem rows22250R_3056 : rowsJ2 104 105 56 58 ≤ 894026330943 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3041
#print axioms SieveCert.rows22250R_3056
