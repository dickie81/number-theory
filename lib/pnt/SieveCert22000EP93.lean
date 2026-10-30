/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 920–929 of 1136

File 93 of 114: the parts `rows22000E_920` … `rows22000E_929` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 255 s of the kernel: row 169 columns 90–96, row 169 columns
97–159, row 169 columns 160–271, row 170 columns 0–42, row 170 columns 43–78, row 170 columns 79–88, row 170 columns
89–95, row 170 columns 96–271, row 171 columns 0–60, row 171 columns 61–78), each a sum of the costs (`rowsJD`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

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

theorem rows22000E_920 : rowsJD 169 170 90 97 ≤ 455718363836970 := by decide +kernel

theorem rows22000E_921 : rowsJD 169 170 97 160 ≤ 4168047107068741 := by decide +kernel

theorem rows22000E_922 : rowsJD 169 170 160 272 ≤ 921511136473011 := by decide +kernel

theorem rows22000E_923 : rowsJD 170 171 0 43 ≤ 29158537600074 := by decide +kernel

theorem rows22000E_924 : rowsJD 170 171 43 79 ≤ 718068107219108 := by decide +kernel

theorem rows22000E_925 : rowsJD 170 171 79 89 ≤ 672017050284339 := by decide +kernel

theorem rows22000E_926 : rowsJD 170 171 89 96 ≤ 533730642644313 := by decide +kernel

theorem rows22000E_927 : rowsJD 170 171 96 272 ≤ 5308945142266088 := by decide +kernel

theorem rows22000E_928 : rowsJD 171 172 0 61 ≤ 30285845056370 := by decide +kernel

theorem rows22000E_929 : rowsJD 171 172 61 79 ≤ 745720067698941 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_920
#print axioms SieveDeep.rows22000E_929
