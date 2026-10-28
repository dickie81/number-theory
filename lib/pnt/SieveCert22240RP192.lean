/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2202–2213 of 5066

File 192 of 387: the parts `rows22240R_2202` … `rows22240R_2213` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 99943 in units of a depth-4 test: row 87 columns 79–79, row 87 columns
80–80, row 87 columns 81–81, row 87 columns 82–82, row 87 columns 83–83, row 87 columns 84–84, row 87 columns 85–85,
row 87 columns 86–86, row 87 columns 87–339, row 88 columns 0–16, row 88 columns 17–19, row 88 columns 20–22), each
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

theorem rows22240R_2202 : rowsJ2 87 88 79 80 ≤ 801712700741 := by decide +kernel

theorem rows22240R_2203 : rowsJ2 87 88 80 81 ≤ 1032821360366 := by decide +kernel

theorem rows22240R_2204 : rowsJ2 87 88 81 82 ≤ 1510942329982 := by decide +kernel

theorem rows22240R_2205 : rowsJ2 87 88 82 83 ≤ 2137454877563 := by decide +kernel

theorem rows22240R_2206 : rowsJ2 87 88 83 84 ≤ 2902828923686 := by decide +kernel

theorem rows22240R_2207 : rowsJ2 87 88 84 85 ≤ 3833120700574 := by decide +kernel

theorem rows22240R_2208 : rowsJ2 87 88 85 86 ≤ 4921066206982 := by decide +kernel

theorem rows22240R_2209 : rowsJ2 87 88 86 87 ≤ 6195715624726 := by decide +kernel

theorem rows22240R_2210 : rowsJ2 87 88 87 340 ≤ 7652823369654 := by decide +kernel

theorem rows22240R_2211 : rowsJ2 88 89 0 17 ≤ 22645793343 := by decide +kernel

theorem rows22240R_2212 : rowsJ2 88 89 17 20 ≤ 0 := by decide +kernel

theorem rows22240R_2213 : rowsJ2 88 89 20 23 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2202
#print axioms SieveCert.rows22240R_2213
