/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3161–3176 of 5066

File 259 of 387: the parts `rows22240R_3161` … `rows22240R_3176` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96564 in units of a depth-4 test: row 109 columns 97–97, row 109
columns 98–98, row 109 columns 99–99, row 109 columns 100–339, row 110 columns 0–24, row 110 columns 25–30, row 110
columns 31–32, row 110 columns 33–34, row 110 columns 35–35, row 110 columns 36–36, row 110 columns 37–37, row 110
columns 38–39, row 110 columns 40–41, row 110 columns 42–43, row 110 columns 44–46, row 110 columns 47–51), each a
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

theorem rows22240R_3161 : rowsJ2 109 110 97 98 ≤ 11147187169780 := by decide +kernel

theorem rows22240R_3162 : rowsJ2 109 110 98 99 ≤ 12602024732572 := by decide +kernel

theorem rows22240R_3163 : rowsJ2 109 110 99 100 ≤ 14135522704842 := by decide +kernel

theorem rows22240R_3164 : rowsJ2 109 110 100 340 ≤ 1002994261956777 := by decide +kernel

theorem rows22240R_3165 : rowsJ2 110 111 0 25 ≤ 0 := by decide +kernel

theorem rows22240R_3166 : rowsJ2 110 111 25 31 ≤ 6733892956591 := by decide +kernel

theorem rows22240R_3167 : rowsJ2 110 111 31 33 ≤ 10516124234153 := by decide +kernel

theorem rows22240R_3168 : rowsJ2 110 111 33 35 ≤ 17527073752790 := by decide +kernel

theorem rows22240R_3169 : rowsJ2 110 111 35 36 ≤ 12038927934453 := by decide +kernel

theorem rows22240R_3170 : rowsJ2 110 111 36 37 ≤ 14743725808921 := by decide +kernel

theorem rows22240R_3171 : rowsJ2 110 111 37 38 ≤ 13615193862755 := by decide +kernel

theorem rows22240R_3172 : rowsJ2 110 111 38 40 ≤ 21372858601882 := by decide +kernel

theorem rows22240R_3173 : rowsJ2 110 111 40 42 ≤ 14657119030148 := by decide +kernel

theorem rows22240R_3174 : rowsJ2 110 111 42 44 ≤ 9583633547539 := by decide +kernel

theorem rows22240R_3175 : rowsJ2 110 111 44 47 ≤ 7270367292811 := by decide +kernel

theorem rows22240R_3176 : rowsJ2 110 111 47 52 ≤ 1394826235304 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3161
#print axioms SieveCert.rows22240R_3176
