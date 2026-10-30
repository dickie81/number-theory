/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 300–309 of 1136

File 31 of 114: the parts `rows22000E_300` … `rows22000E_309` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 275 s of the kernel: row 91 columns 89–271, row 92 columns 0–37,
row 92 columns 38–48, row 92 columns 49–57, row 92 columns 58–68, row 92 columns 69–77, row 92 columns 78–84, row 92
columns 85–89, row 92 columns 90–271, row 93 columns 0–37), each a sum of the costs (`rowsJD`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22000E.lean`.
-/
import SieveGrid22000E

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveDeep

open SieveCert

section

attribute [local instance] grid22000E ibPar22000E

theorem rows22000E_300 : rowsJD 91 92 89 272 ≤ 67217818092087 := by decide +kernel

theorem rows22000E_301 : rowsJD 92 93 0 38 ≤ 173668495978187 := by decide +kernel

theorem rows22000E_302 : rowsJD 92 93 38 49 ≤ 118002866856492 := by decide +kernel

theorem rows22000E_303 : rowsJD 92 93 49 58 ≤ 117930098571224 := by decide +kernel

theorem rows22000E_304 : rowsJD 92 93 58 69 ≤ 120444587978113 := by decide +kernel

theorem rows22000E_305 : rowsJD 92 93 69 78 ≤ 52996619586039 := by decide +kernel

theorem rows22000E_306 : rowsJD 92 93 78 85 ≤ 31365329113260 := by decide +kernel

theorem rows22000E_307 : rowsJD 92 93 85 90 ≤ 53287110538665 := by decide +kernel

theorem rows22000E_308 : rowsJD 92 93 90 272 ≤ 81515471500215 := by decide +kernel

theorem rows22000E_309 : rowsJD 93 94 0 38 ≤ 168920791633211 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_300
#print axioms SieveDeep.rows22000E_309
