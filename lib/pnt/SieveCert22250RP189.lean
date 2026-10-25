/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2278–2292 of 4715

File 189 of 351: the parts `rows22250R_2278` … `rows22250R_2292` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94337 tests: row 92 columns 44–44, row 92 columns 45–45, row 92 columns
46–46, row 92 columns 47–47, row 92 columns 48–48, row 92 columns 49–49, row 92 columns 50–50, row 92 columns 51–51,
row 92 columns 52–52, row 92 columns 53–54, row 92 columns 55–56, row 92 columns 57–58, row 92 columns 59–61, row 92
columns 62–66, row 92 columns 67–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2278 : rowsJ2 92 93 44 45 ≤ 15832626720596 := by decide +kernel

theorem rows22250R_2279 : rowsJ2 92 93 45 46 ≤ 14072633467761 := by decide +kernel

theorem rows22250R_2280 : rowsJ2 92 93 46 47 ≤ 12332809621445 := by decide +kernel

theorem rows22250R_2281 : rowsJ2 92 93 47 48 ≤ 10671589189349 := by decide +kernel

theorem rows22250R_2282 : rowsJ2 92 93 48 49 ≤ 9125991872345 := by decide +kernel

theorem rows22250R_2283 : rowsJ2 92 93 49 50 ≤ 5865156694859 := by decide +kernel

theorem rows22250R_2284 : rowsJ2 92 93 50 51 ≤ 3461877513961 := by decide +kernel

theorem rows22250R_2285 : rowsJ2 92 93 51 52 ≤ 1388538819130 := by decide +kernel

theorem rows22250R_2286 : rowsJ2 92 93 52 53 ≤ 0 := by decide +kernel

theorem rows22250R_2287 : rowsJ2 92 93 53 55 ≤ 0 := by decide +kernel

theorem rows22250R_2288 : rowsJ2 92 93 55 57 ≤ 0 := by decide +kernel

theorem rows22250R_2289 : rowsJ2 92 93 57 59 ≤ 0 := by decide +kernel

theorem rows22250R_2290 : rowsJ2 92 93 59 62 ≤ 0 := by decide +kernel

theorem rows22250R_2291 : rowsJ2 92 93 62 67 ≤ 0 := by decide +kernel

theorem rows22250R_2292 : rowsJ2 92 93 67 73 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2278
#print axioms SieveCert.rows22250R_2292
