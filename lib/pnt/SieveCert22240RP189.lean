/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2161–2172 of 5066

File 189 of 387: the parts `rows22240R_2161` … `rows22240R_2172` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 97884 in units of a depth-4 test: row 86 columns 82–82, row 86 columns
83–83, row 86 columns 84–84, row 86 columns 85–85, row 86 columns 86–339, row 87 columns 0–16, row 87 columns 17–19,
row 87 columns 20–21, row 87 columns 22–24, row 87 columns 25–28, row 87 columns 29–33, row 87 columns 34–36), each
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

theorem rows22240R_2161 : rowsJ2 86 87 82 83 ≤ 2150097938508 := by decide +kernel

theorem rows22240R_2162 : rowsJ2 86 87 83 84 ≤ 2914593273928 := by decide +kernel

theorem rows22240R_2163 : rowsJ2 86 87 84 85 ≤ 3841927287517 := by decide +kernel

theorem rows22240R_2164 : rowsJ2 86 87 85 86 ≤ 4924127958080 := by decide +kernel

theorem rows22240R_2165 : rowsJ2 86 87 86 340 ≤ 6189869373112 := by decide +kernel

theorem rows22240R_2166 : rowsJ2 87 88 0 17 ≤ 37869094244 := by decide +kernel

theorem rows22240R_2167 : rowsJ2 87 88 17 20 ≤ 1959524409 := by decide +kernel

theorem rows22240R_2168 : rowsJ2 87 88 20 22 ≤ 0 := by decide +kernel

theorem rows22240R_2169 : rowsJ2 87 88 22 25 ≤ 0 := by decide +kernel

theorem rows22240R_2170 : rowsJ2 87 88 25 29 ≤ 0 := by decide +kernel

theorem rows22240R_2171 : rowsJ2 87 88 29 34 ≤ 385558933165 := by decide +kernel

theorem rows22240R_2172 : rowsJ2 87 88 34 37 ≤ 5786540858277 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2161
#print axioms SieveCert.rows22240R_2172
