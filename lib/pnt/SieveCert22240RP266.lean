/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3268–3283 of 5066

File 266 of 387: the parts `rows22240R_3268` … `rows22240R_3283` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 97483 in units of a depth-4 test: row 113 columns 78–80, row 113
columns 81–83, row 113 columns 84–86, row 113 columns 87–88, row 113 columns 89–90, row 113 columns 91–92, row 113
columns 93–93, row 113 columns 94–94, row 113 columns 95–95, row 113 columns 96–96, row 113 columns 97–97, row 113
columns 98–339, row 114 columns 0–26, row 114 columns 27–30, row 114 columns 31–32, row 114 columns 33–34), each a
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

theorem rows22240R_3268 : rowsJ2 113 114 78 81 ≤ 91913911506 := by decide +kernel

theorem rows22240R_3269 : rowsJ2 113 114 81 84 ≤ 1188378666903 := by decide +kernel

theorem rows22240R_3270 : rowsJ2 113 114 84 87 ≤ 4596911498614 := by decide +kernel

theorem rows22240R_3271 : rowsJ2 113 114 87 89 ≤ 6001836433918 := by decide +kernel

theorem rows22240R_3272 : rowsJ2 113 114 89 91 ≤ 9140505564642 := by decide +kernel

theorem rows22240R_3273 : rowsJ2 113 114 91 93 ≤ 12996715763624 := by decide +kernel

theorem rows22240R_3274 : rowsJ2 113 114 93 94 ≤ 8174307407969 := by decide +kernel

theorem rows22240R_3275 : rowsJ2 113 114 94 95 ≤ 9442125054586 := by decide +kernel

theorem rows22240R_3276 : rowsJ2 113 114 95 96 ≤ 10786568932418 := by decide +kernel

theorem rows22240R_3277 : rowsJ2 113 114 96 97 ≤ 12266108790730 := by decide +kernel

theorem rows22240R_3278 : rowsJ2 113 114 97 98 ≤ 13829442783645 := by decide +kernel

theorem rows22240R_3279 : rowsJ2 113 114 98 340 ≤ 1536173677812190 := by decide +kernel

theorem rows22240R_3280 : rowsJ2 114 115 0 27 ≤ 704521705111 := by decide +kernel

theorem rows22240R_3281 : rowsJ2 114 115 27 31 ≤ 10413044343387 := by decide +kernel

theorem rows22240R_3282 : rowsJ2 114 115 31 33 ≤ 14104314935482 := by decide +kernel

theorem rows22240R_3283 : rowsJ2 114 115 33 35 ≤ 22963897800189 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3268
#print axioms SieveCert.rows22240R_3283
