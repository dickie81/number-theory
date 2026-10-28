/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2178–2186 of 4715

File 181 of 351: the parts `rows22250R_2178` … `rows22250R_2186` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 95322 in units of a depth-4 test: row 89 columns 86–86, row 89 columns
87–87, row 89 columns 88–88, row 89 columns 89–339, row 90 columns 0–15, row 90 columns 16–19, row 90 columns 20–24,
row 90 columns 25–31, row 90 columns 32–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2178 : rowsJ2 89 90 86 87 ≤ 6262767353771 := by decide +kernel

theorem rows22250R_2179 : rowsJ2 89 90 87 88 ≤ 7450594442637 := by decide +kernel

theorem rows22250R_2180 : rowsJ2 89 90 88 89 ≤ 7542343892156 := by decide +kernel

theorem rows22250R_2181 : rowsJ2 89 90 89 340 ≤ 6754509716500 := by decide +kernel

theorem rows22250R_2182 : rowsJ2 90 91 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2183 : rowsJ2 90 91 16 20 ≤ 0 := by decide +kernel

theorem rows22250R_2184 : rowsJ2 90 91 20 25 ≤ 0 := by decide +kernel

theorem rows22250R_2185 : rowsJ2 90 91 25 32 ≤ 202068246882 := by decide +kernel

theorem rows22250R_2186 : rowsJ2 90 91 32 36 ≤ 8711575894340 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2178
#print axioms SieveCert.rows22250R_2186
