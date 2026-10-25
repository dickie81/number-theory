/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4017–4032 of 4715

File 307 of 351: the parts `rows22250R_4017` … `rows22250R_4032` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 94986 tests: row 151 columns 63–63, row 151 columns 64–64, row 151 columns
65–66, row 151 columns 67–68, row 151 columns 69–72, row 151 columns 73–339, row 152 columns 0–42, row 152 columns
43–45, row 152 columns 46–47, row 152 columns 48–48, row 152 columns 49–49, row 152 columns 50–50, row 152 columns
51–51, row 152 columns 52–52, row 152 columns 53–53, row 152 columns 54–54), each a sum of refined costs (`rows2` or
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

theorem rows22250R_4017 : rowsJ2 151 152 63 64 ≤ 7056035143991 := by decide +kernel

theorem rows22250R_4018 : rowsJ2 151 152 64 65 ≤ 6060392018405 := by decide +kernel

theorem rows22250R_4019 : rowsJ2 151 152 65 67 ≤ 9454449971792 := by decide +kernel

theorem rows22250R_4020 : rowsJ2 151 152 67 69 ≤ 6418513003713 := by decide +kernel

theorem rows22250R_4021 : rowsJ2 151 152 69 73 ≤ 6131961421438 := by decide +kernel

theorem rows22250R_4022 : rowsJ2 151 152 73 340 ≤ 2119736640828927 := by decide +kernel

theorem rows22250R_4023 : rowsJ2 152 153 0 43 ≤ 5394050508541 := by decide +kernel

theorem rows22250R_4024 : rowsJ2 152 153 43 46 ≤ 9881207109919 := by decide +kernel

theorem rows22250R_4025 : rowsJ2 152 153 46 48 ≤ 10537616412402 := by decide +kernel

theorem rows22250R_4026 : rowsJ2 152 153 48 49 ≤ 6634949282684 := by decide +kernel

theorem rows22250R_4027 : rowsJ2 152 153 49 50 ≤ 7619974317806 := by decide +kernel

theorem rows22250R_4028 : rowsJ2 152 153 50 51 ≤ 8657794372306 := by decide +kernel

theorem rows22250R_4029 : rowsJ2 152 153 51 52 ≤ 9746322803335 := by decide +kernel

theorem rows22250R_4030 : rowsJ2 152 153 52 53 ≤ 10883656847038 := by decide +kernel

theorem rows22250R_4031 : rowsJ2 152 153 53 54 ≤ 12068067869365 := by decide +kernel

theorem rows22250R_4032 : rowsJ2 152 153 54 55 ≤ 13297992557252 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4017
#print axioms SieveCert.rows22250R_4032
