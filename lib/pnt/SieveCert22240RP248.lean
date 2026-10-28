/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2986–3001 of 5066

File 248 of 387: the parts `rows22240R_2986` … `rows22240R_3001` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96848 in units of a depth-4 test: row 104 columns 102–339, row 105
columns 0–18, row 105 columns 19–29, row 105 columns 30–32, row 105 columns 33–34, row 105 columns 35–36, row 105
columns 37–37, row 105 columns 38–38, row 105 columns 39–39, row 105 columns 40–40, row 105 columns 41–41, row 105
columns 42–42, row 105 columns 43–44, row 105 columns 45–46, row 105 columns 47–48, row 105 columns 49–51), each a
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

theorem rows22240R_2986 : rowsJ2 104 105 102 340 ≤ 278795984399140 := by decide +kernel

theorem rows22240R_2987 : rowsJ2 105 106 0 19 ≤ 0 := by decide +kernel

theorem rows22240R_2988 : rowsJ2 105 106 19 30 ≤ 743720463286 := by decide +kernel

theorem rows22240R_2989 : rowsJ2 105 106 30 33 ≤ 8475016596107 := by decide +kernel

theorem rows22240R_2990 : rowsJ2 105 106 33 35 ≤ 12745110753662 := by decide +kernel

theorem rows22240R_2991 : rowsJ2 105 106 35 37 ≤ 20498590480944 := by decide +kernel

theorem rows22240R_2992 : rowsJ2 105 106 37 38 ≤ 13412255736499 := by decide +kernel

theorem rows22240R_2993 : rowsJ2 105 106 38 39 ≤ 15150784262617 := by decide +kernel

theorem rows22240R_2994 : rowsJ2 105 106 39 40 ≤ 14973868408680 := by decide +kernel

theorem rows22240R_2995 : rowsJ2 105 106 40 41 ≤ 12947833669968 := by decide +kernel

theorem rows22240R_2996 : rowsJ2 105 106 41 42 ≤ 11121230285389 := by decide +kernel

theorem rows22240R_2997 : rowsJ2 105 106 42 43 ≤ 9489059801172 := by decide +kernel

theorem rows22240R_2998 : rowsJ2 105 106 43 45 ≤ 14735008506360 := by decide +kernel

theorem rows22240R_2999 : rowsJ2 105 106 45 47 ≤ 9636304110074 := by decide +kernel

theorem rows22240R_3000 : rowsJ2 105 106 47 49 ≤ 5317595374341 := by decide +kernel

theorem rows22240R_3001 : rowsJ2 105 106 49 52 ≤ 2950084579162 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2986
#print axioms SieveCert.rows22240R_3001
