/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 3017–3027 of 5796

File 272 of 465: the parts `rows22250R_3017` … `rows22250R_3027` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 97795 tests: row 103 columns 85–85, row 103 columns 86–86, row 103 columns
87–87, row 103 columns 88–88, row 103 columns 89–89, row 103 columns 90–90, row 103 columns 91–91, row 103 columns
92–92, row 103 columns 93–93, row 103 columns 94–94, row 103 columns 95–95), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3017 : rowsJ2 103 104 85 86 ≤ 1110920161530 := by decide +kernel

theorem rows22250R_3018 : rowsJ2 103 104 86 87 ≤ 1487199198446 := by decide +kernel

theorem rows22250R_3019 : rowsJ2 103 104 87 88 ≤ 1987384658418 := by decide +kernel

theorem rows22250R_3020 : rowsJ2 103 104 88 89 ≤ 2395844318141 := by decide +kernel

theorem rows22250R_3021 : rowsJ2 103 104 89 90 ≤ 2574029603570 := by decide +kernel

theorem rows22250R_3022 : rowsJ2 103 104 90 91 ≤ 2420716408461 := by decide +kernel

theorem rows22250R_3023 : rowsJ2 103 104 91 92 ≤ 2265769787804 := by decide +kernel

theorem rows22250R_3024 : rowsJ2 103 104 92 93 ≤ 2183014484411 := by decide +kernel

theorem rows22250R_3025 : rowsJ2 103 104 93 94 ≤ 2160437151222 := by decide +kernel

theorem rows22250R_3026 : rowsJ2 103 104 94 95 ≤ 2212990566213 := by decide +kernel

theorem rows22250R_3027 : rowsJ2 103 104 95 96 ≤ 2329812044898 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3017
#print axioms SieveCert.rows22250R_3027
