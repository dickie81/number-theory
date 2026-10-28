/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4300–4314 of 4715

File 326 of 351: the parts `rows22250R_4300` … `rows22250R_4314` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 97500 in units of a depth-4 test: row 165 columns 45–45, row 165
columns 46–46, row 165 columns 47–47, row 165 columns 48–48, row 165 columns 49–49, row 165 columns 50–50, row 165
columns 51–51, row 165 columns 52–52, row 165 columns 53–53, row 165 columns 54–54, row 165 columns 55–55, row 165
columns 56–57, row 165 columns 58–59, row 165 columns 60–339, row 166 columns 0–38), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4300 : rowsJ2 165 166 45 46 ≤ 13150521226130 := by decide +kernel

theorem rows22250R_4301 : rowsJ2 165 166 46 47 ≤ 14618425245900 := by decide +kernel

theorem rows22250R_4302 : rowsJ2 165 166 47 48 ≤ 16143735842978 := by decide +kernel

theorem rows22250R_4303 : rowsJ2 165 166 48 49 ≤ 17724677355678 := by decide +kernel

theorem rows22250R_4304 : rowsJ2 165 166 49 50 ≤ 19359694109595 := by decide +kernel

theorem rows22250R_4305 : rowsJ2 165 166 50 51 ≤ 19160175755916 := by decide +kernel

theorem rows22250R_4306 : rowsJ2 165 166 51 52 ≤ 17182263117056 := by decide +kernel

theorem rows22250R_4307 : rowsJ2 165 166 52 53 ≤ 15328660313208 := by decide +kernel

theorem rows22250R_4308 : rowsJ2 165 166 53 54 ≤ 13595464324072 := by decide +kernel

theorem rows22250R_4309 : rowsJ2 165 166 54 55 ≤ 11979065454671 := by decide +kernel

theorem rows22250R_4310 : rowsJ2 165 166 55 56 ≤ 10476131567365 := by decide +kernel

theorem rows22250R_4311 : rowsJ2 165 166 56 58 ≤ 16882227888737 := by decide +kernel

theorem rows22250R_4312 : rowsJ2 165 166 58 60 ≤ 12160032648090 := by decide +kernel

theorem rows22250R_4313 : rowsJ2 165 166 60 340 ≤ 2664142949144748 := by decide +kernel

theorem rows22250R_4314 : rowsJ2 166 167 0 39 ≤ 17037437842133 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4300
#print axioms SieveCert.rows22250R_4314
