/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3034–3049 of 5066

File 251 of 387: the parts `rows22240R_3034` … `rows22240R_3049` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97522 in units of a depth-4 test: row 106 columns 39–39, row 106
columns 40–40, row 106 columns 41–41, row 106 columns 42–43, row 106 columns 44–45, row 106 columns 46–47, row 106
columns 48–50, row 106 columns 51–55, row 106 columns 56–64, row 106 columns 65–70, row 106 columns 71–74, row 106
columns 75–77, row 106 columns 78–79, row 106 columns 80–80, row 106 columns 81–81, row 106 columns 82–82), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
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

theorem rows22240R_3034 : rowsJ2 106 107 39 40 ≤ 13789933190873 := by decide +kernel

theorem rows22240R_3035 : rowsJ2 106 107 40 41 ≤ 11831242620823 := by decide +kernel

theorem rows22240R_3036 : rowsJ2 106 107 41 42 ≤ 10073310972725 := by decide +kernel

theorem rows22240R_3037 : rowsJ2 106 107 42 44 ≤ 15651946867244 := by decide +kernel

theorem rows22240R_3038 : rowsJ2 106 107 44 46 ≤ 10508812495005 := by decide +kernel

theorem rows22240R_3039 : rowsJ2 106 107 46 48 ≤ 6048704222093 := by decide +kernel

theorem rows22240R_3040 : rowsJ2 106 107 48 51 ≤ 3254830317602 := by decide +kernel

theorem rows22240R_3041 : rowsJ2 106 107 51 56 ≤ 377156648272 := by decide +kernel

theorem rows22240R_3042 : rowsJ2 106 107 56 65 ≤ 177826672584 := by decide +kernel

theorem rows22240R_3043 : rowsJ2 106 107 65 71 ≤ 0 := by decide +kernel

theorem rows22240R_3044 : rowsJ2 106 107 71 75 ≤ 0 := by decide +kernel

theorem rows22240R_3045 : rowsJ2 106 107 75 78 ≤ 218993333983 := by decide +kernel

theorem rows22240R_3046 : rowsJ2 106 107 78 80 ≤ 913739257082 := by decide +kernel

theorem rows22240R_3047 : rowsJ2 106 107 80 81 ≤ 873179258554 := by decide +kernel

theorem rows22240R_3048 : rowsJ2 106 107 81 82 ≤ 770186350112 := by decide +kernel

theorem rows22240R_3049 : rowsJ2 106 107 82 83 ≤ 722415728931 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3034
#print axioms SieveCert.rows22240R_3049
