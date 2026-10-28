/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 4051–4063 of 5066

File 320 of 387: the parts `rows22240R_4051` … `rows22240R_4063` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 95392 in units of a depth-4 test: row 141 columns 48–50, row 141
columns 51–52, row 141 columns 53–53, row 141 columns 54–54, row 141 columns 55–55, row 141 columns 56–56, row 141
columns 57–57, row 141 columns 58–58, row 141 columns 59–59, row 141 columns 60–60, row 141 columns 61–61, row 141
columns 62–62, row 141 columns 63–63), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_4051 : rowsJ2 141 142 48 51 ≤ 6418213109210 := by decide +kernel

theorem rows22240R_4052 : rowsJ2 141 142 51 53 ≤ 7266139891044 := by decide +kernel

theorem rows22240R_4053 : rowsJ2 141 142 53 54 ≤ 4688347744287 := by decide +kernel

theorem rows22240R_4054 : rowsJ2 141 142 54 55 ≤ 5457251179349 := by decide +kernel

theorem rows22240R_4055 : rowsJ2 141 142 55 56 ≤ 6272634030989 := by decide +kernel

theorem rows22240R_4056 : rowsJ2 141 142 56 57 ≤ 7132620387723 := by decide +kernel

theorem rows22240R_4057 : rowsJ2 141 142 57 58 ≤ 8035455919376 := by decide +kernel

theorem rows22240R_4058 : rowsJ2 141 142 58 59 ≤ 8979501796591 := by decide +kernel

theorem rows22240R_4059 : rowsJ2 141 142 59 60 ≤ 9963223382371 := by decide +kernel

theorem rows22240R_4060 : rowsJ2 141 142 60 61 ≤ 10985183850351 := by decide +kernel

theorem rows22240R_4061 : rowsJ2 141 142 61 62 ≤ 12024208741397 := by decide +kernel

theorem rows22240R_4062 : rowsJ2 141 142 62 63 ≤ 13020258849649 := by decide +kernel

theorem rows22240R_4063 : rowsJ2 141 142 63 64 ≤ 12840699847251 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_4051
#print axioms SieveCert.rows22240R_4063
