/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2225–2239 of 4715

File 185 of 351: the parts `rows22250R_2225` … `rows22250R_2239` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94904 tests: row 91 columns 16–19, row 91 columns 20–25, row 91 columns
26–32, row 91 columns 33–35, row 91 columns 36–37, row 91 columns 38–38, row 91 columns 39–39, row 91 columns 40–40,
row 91 columns 41–41, row 91 columns 42–42, row 91 columns 43–43, row 91 columns 44–44, row 91 columns 45–45, row 91
columns 46–46, row 91 columns 47–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2225 : rowsJ2 91 92 16 20 ≤ 0 := by decide +kernel

theorem rows22250R_2226 : rowsJ2 91 92 20 26 ≤ 0 := by decide +kernel

theorem rows22250R_2227 : rowsJ2 91 92 26 33 ≤ 1516188215843 := by decide +kernel

theorem rows22250R_2228 : rowsJ2 91 92 33 36 ≤ 8584690066745 := by decide +kernel

theorem rows22250R_2229 : rowsJ2 91 92 36 38 ≤ 12662856520899 := by decide +kernel

theorem rows22250R_2230 : rowsJ2 91 92 38 39 ≤ 8296224811041 := by decide +kernel

theorem rows22250R_2231 : rowsJ2 91 92 39 40 ≤ 9601033983043 := by decide +kernel

theorem rows22250R_2232 : rowsJ2 91 92 40 41 ≤ 11025620099721 := by decide +kernel

theorem rows22250R_2233 : rowsJ2 91 92 41 42 ≤ 12564068493921 := by decide +kernel

theorem rows22250R_2234 : rowsJ2 91 92 42 43 ≤ 14210967326473 := by decide +kernel

theorem rows22250R_2235 : rowsJ2 91 92 43 44 ≤ 15628299837664 := by decide +kernel

theorem rows22250R_2236 : rowsJ2 91 92 44 45 ≤ 16817985332466 := by decide +kernel

theorem rows22250R_2237 : rowsJ2 91 92 45 46 ≤ 14994907589285 := by decide +kernel

theorem rows22250R_2238 : rowsJ2 91 92 46 47 ≤ 13251456461277 := by decide +kernel

theorem rows22250R_2239 : rowsJ2 91 92 47 48 ≤ 11527481775649 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2225
#print axioms SieveCert.rows22250R_2239
