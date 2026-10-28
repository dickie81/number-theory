/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2255–2267 of 5066

File 196 of 387: the parts `rows22240R_2255` … `rows22240R_2267` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 94392 in units of a depth-4 test: row 88 columns 88–339, row 89 columns
0–16, row 89 columns 17–19, row 89 columns 20–22, row 89 columns 23–26, row 89 columns 27–31, row 89 columns 32–35,
row 89 columns 36–37, row 89 columns 38–39, row 89 columns 40–40, row 89 columns 41–41, row 89 columns 42–42, row 89
columns 43–43), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2255 : rowsJ2 88 89 88 340 ≤ 9269101262467 := by decide +kernel

theorem rows22240R_2256 : rowsJ2 89 90 0 17 ≤ 10421080903 := by decide +kernel

theorem rows22240R_2257 : rowsJ2 89 90 17 20 ≤ 0 := by decide +kernel

theorem rows22240R_2258 : rowsJ2 89 90 20 23 ≤ 0 := by decide +kernel

theorem rows22240R_2259 : rowsJ2 89 90 23 27 ≤ 0 := by decide +kernel

theorem rows22240R_2260 : rowsJ2 89 90 27 32 ≤ 0 := by decide +kernel

theorem rows22240R_2261 : rowsJ2 89 90 32 36 ≤ 4759453646848 := by decide +kernel

theorem rows22240R_2262 : rowsJ2 89 90 36 38 ≤ 8542136787082 := by decide +kernel

theorem rows22240R_2263 : rowsJ2 89 90 38 40 ≤ 13399840369167 := by decide +kernel

theorem rows22240R_2264 : rowsJ2 89 90 40 41 ≤ 8625679713153 := by decide +kernel

theorem rows22240R_2265 : rowsJ2 89 90 41 42 ≤ 9934569068276 := by decide +kernel

theorem rows22240R_2266 : rowsJ2 89 90 42 43 ≤ 11258367247462 := by decide +kernel

theorem rows22240R_2267 : rowsJ2 89 90 43 44 ≤ 12594290111691 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2255
#print axioms SieveCert.rows22240R_2267
